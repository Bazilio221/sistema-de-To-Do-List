#!/usr/bin/env python3
"""
Sistema de To-Do List (CLI)

- CRUD completo de tarefas e categorias
- POO: entidades, serviços, repositório abstrato (polimorfismo), exceção própria
- Estruturas de dados:
    dict  -> índice por id (busca O(1)) de tarefas, categorias e usuários
    set   -> garantia de nomes de categoria únicos
    deque -> pilha de "desfazer exclusão" (LIFO, tamanho limitado)
    heap  -> fila de prioridade para ordenar a listagem
- Persistência em JSON com escrita atômica
- Login com senha protegida (PBKDF2-SHA256 + salt aleatório)

Uso: python todo_system.py
"""
from __future__ import annotations

import getpass
import hashlib
import heapq
import hmac
import json
import os
import re
import secrets
from abc import ABC, abstractmethod
from collections import deque
from dataclasses import asdict, dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Callable, Optional

ARQUIVO_DADOS = Path(__file__).with_name("dados.json")
PRIORIDADES = {1: "Alta", 2: "Média", 3: "Baixa"}
_MANTER = object()  # sentinela: "não alterar este campo"


class ErroValidacao(Exception):
    """Erro de regra de negócio, mostrado ao usuário sem derrubar o programa."""


# ----------------------------------------------------------------- ENTIDADES
@dataclass
class Categoria:
    id: int
    nome: str


@dataclass
class Tarefa:
    id: int
    titulo: str
    descricao: str = ""
    categoria_id: Optional[int] = None
    prioridade: int = 2
    concluida: bool = False
    criada_em: str = field(
        default_factory=lambda: datetime.now().isoformat(timespec="seconds")
    )

    def alternar(self) -> None:
        self.concluida = not self.concluida

    def to_dict(self) -> dict:
        return asdict(self)

    @classmethod
    def from_dict(cls, d: dict) -> "Tarefa":
        return cls(**d)


class Usuario:
    """Dono de um conjunto de tarefas e categorias. A senha nunca é guardada em texto."""

    def __init__(self, username, salt, senha_hash, tarefas=None, categorias=None,
                 prox_tarefa=1, prox_categoria=1):
        self.username: str = username
        self._salt: str = salt
        self._senha_hash: str = senha_hash
        self.tarefas: dict[int, Tarefa] = tarefas or {}
        self.categorias: dict[int, Categoria] = categorias or {}
        self.prox_tarefa: int = prox_tarefa
        self.prox_categoria: int = prox_categoria

    @staticmethod
    def _derivar(senha: str, salt: str) -> str:
        return hashlib.pbkdf2_hmac(
            "sha256", senha.encode(), bytes.fromhex(salt), 200_000
        ).hex()

    @classmethod
    def novo(cls, username: str, senha: str) -> "Usuario":
        salt = secrets.token_hex(16)
        return cls(username, salt, cls._derivar(senha, salt))

    def verificar_senha(self, senha: str) -> bool:
        return hmac.compare_digest(self._senha_hash, self._derivar(senha, self._salt))

    def to_dict(self) -> dict:
        return {
            "username": self.username,
            "salt": self._salt,
            "senha_hash": self._senha_hash,
            "prox_tarefa": self.prox_tarefa,
            "prox_categoria": self.prox_categoria,
            "tarefas": {str(i): t.to_dict() for i, t in self.tarefas.items()},
            "categorias": {str(i): asdict(c) for i, c in self.categorias.items()},
        }

    @classmethod
    def from_dict(cls, d: dict) -> "Usuario":
        return cls(
            d["username"], d["salt"], d["senha_hash"],
            {int(i): Tarefa.from_dict(t) for i, t in d["tarefas"].items()},
            {int(i): Categoria(**c) for i, c in d["categorias"].items()},
            d["prox_tarefa"], d["prox_categoria"],
        )


# --------------------------------------------------------------- PERSISTÊNCIA
class Repositorio(ABC):
    """Abstração: o resto do sistema não sabe se os dados vão para JSON, SQLite, etc."""

    @abstractmethod
    def carregar(self) -> dict[str, Usuario]: ...

    @abstractmethod
    def salvar(self, usuarios: dict[str, Usuario]) -> None: ...


class RepositorioJSON(Repositorio):
    def __init__(self, caminho: Path):
        self.caminho = caminho

    def carregar(self) -> dict[str, Usuario]:
        if not self.caminho.exists():
            return {}
        try:
            bruto = json.loads(self.caminho.read_text(encoding="utf-8"))
            return {u["username"]: Usuario.from_dict(u) for u in bruto["usuarios"]}
        except (json.JSONDecodeError, KeyError, TypeError):
            backup = self.caminho.with_suffix(".corrompido")
            os.replace(self.caminho, backup)
            print(f"Arquivo de dados inválido; cópia guardada em {backup.name}.")
            return {}

    def salvar(self, usuarios: dict[str, Usuario]) -> None:
        dados = {"usuarios": [u.to_dict() for u in usuarios.values()]}
        tmp = self.caminho.with_suffix(".tmp")
        tmp.write_text(json.dumps(dados, ensure_ascii=False, indent=2), encoding="utf-8")
        os.replace(tmp, self.caminho)  # troca atômica: nunca deixa o arquivo pela metade


# ------------------------------------------------------------------- SERVIÇOS
class ServicoAuth:
    def __init__(self, usuarios: dict[str, Usuario], persistir: Callable[[], None]):
        self.usuarios = usuarios
        self._persistir = persistir

    def cadastrar(self, username: str, senha: str) -> Usuario:
        username = username.strip().lower()
        if not re.fullmatch(r"[a-z0-9_]{3,20}", username):
            raise ErroValidacao("Usuário: 3 a 20 caracteres (letras, números ou _).")
        if len(senha) < 6:
            raise ErroValidacao("A senha precisa ter pelo menos 6 caracteres.")
        if username in self.usuarios:
            raise ErroValidacao("Esse usuário já existe.")
        usuario = Usuario.novo(username, senha)
        self.usuarios[username] = usuario
        self._persistir()
        return usuario

    def login(self, username: str, senha: str) -> Usuario:
        usuario = self.usuarios.get(username.strip().lower())
        if usuario is None or not usuario.verificar_senha(senha):
            raise ErroValidacao("Usuário ou senha incorretos.")
        return usuario


class GerenciadorTarefas:
    """Regras de negócio (CRUD) das tarefas e categorias de UM usuário."""

    def __init__(self, usuario: Usuario, persistir: Callable[[], None]):
        self.u = usuario
        self._persistir = persistir
        self._lixeira: deque[Tarefa] = deque(maxlen=10)  # pilha de desfazer

    # ---- categorias
    def criar_categoria(self, nome: str) -> Categoria:
        nome = nome.strip()
        self._validar_nome_categoria(nome)
        cat = Categoria(self.u.prox_categoria, nome)
        self.u.categorias[cat.id] = cat
        self.u.prox_categoria += 1
        self._persistir()
        return cat

    def listar_categorias(self) -> list[Categoria]:
        return sorted(self.u.categorias.values(), key=lambda c: c.nome.lower())

    def renomear_categoria(self, cid: int, nome: str) -> None:
        cat = self._categoria(cid)
        nome = nome.strip()
        self._validar_nome_categoria(nome)
        cat.nome = nome
        self._persistir()

    def excluir_categoria(self, cid: int) -> int:
        """Remove a categoria; suas tarefas ficam sem categoria. Retorna quantas foram afetadas."""
        self._categoria(cid)
        afetadas = [t for t in self.u.tarefas.values() if t.categoria_id == cid]
        for t in afetadas:
            t.categoria_id = None
        del self.u.categorias[cid]
        self._persistir()
        return len(afetadas)

    def nome_categoria(self, cid: Optional[int]) -> str:
        return self.u.categorias[cid].nome if cid in self.u.categorias else "Sem categoria"

    # ---- tarefas
    def criar_tarefa(self, titulo, descricao="", categoria_id=None, prioridade=2) -> Tarefa:
        titulo = titulo.strip()
        if not titulo:
            raise ErroValidacao("O título não pode ser vazio.")
        self._validar_refs(categoria_id, prioridade)
        t = Tarefa(self.u.prox_tarefa, titulo, descricao.strip(), categoria_id, prioridade)
        self.u.tarefas[t.id] = t
        self.u.prox_tarefa += 1
        self._persistir()
        return t

    def obter(self, tid: int) -> Tarefa:
        t = self.u.tarefas.get(tid)
        if t is None:
            raise ErroValidacao(f"Tarefa #{tid} não encontrada.")
        return t

    def listar(self, status: Optional[str] = None, categoria_id: Optional[int] = None):
        """status: None | 'pendentes' | 'concluidas'. Ordena por (pendente primeiro, prioridade, id)."""
        heap = []
        for t in self.u.tarefas.values():
            if status == "pendentes" and t.concluida:
                continue
            if status == "concluidas" and not t.concluida:
                continue
            if categoria_id is not None and t.categoria_id != categoria_id:
                continue
            heap.append((t.concluida, t.prioridade, t.id))
        heapq.heapify(heap)
        return [self.u.tarefas[heapq.heappop(heap)[2]] for _ in range(len(heap))]

    def atualizar(self, tid, titulo=None, descricao=None, prioridade=None, categoria_id=_MANTER):
        t = self.obter(tid)
        if titulo is not None and not titulo.strip():
            raise ErroValidacao("O título não pode ser vazio.")
        nova_cat = t.categoria_id if categoria_id is _MANTER else categoria_id
        nova_prio = t.prioridade if prioridade is None else prioridade
        self._validar_refs(nova_cat, nova_prio)
        if titulo is not None:
            t.titulo = titulo.strip()
        if descricao is not None:
            t.descricao = descricao.strip()
        t.categoria_id, t.prioridade = nova_cat, nova_prio
        self._persistir()
        return t

    def alternar(self, tid: int) -> Tarefa:
        t = self.obter(tid)
        t.alternar()
        self._persistir()
        return t

    def excluir_tarefa(self, tid: int) -> Tarefa:
        t = self.obter(tid)
        del self.u.tarefas[tid]
        self._lixeira.append(t)
        self._persistir()
        return t

    def desfazer_exclusao(self) -> Tarefa:
        if not self._lixeira:
            raise ErroValidacao("Nada para desfazer nesta sessão.")
        t = self._lixeira.pop()
        if t.categoria_id not in self.u.categorias:
            t.categoria_id = None
        self.u.tarefas[t.id] = t
        self._persistir()
        return t

    # ---- validações internas
    def _categoria(self, cid: int) -> Categoria:
        cat = self.u.categorias.get(cid)
        if cat is None:
            raise ErroValidacao(f"Categoria #{cid} não encontrada.")
        return cat

    def _validar_nome_categoria(self, nome: str) -> None:
        if not nome:
            raise ErroValidacao("O nome da categoria não pode ser vazio.")
        existentes = {c.nome.lower() for c in self.u.categorias.values()}  # set
        if nome.lower() in existentes:
            raise ErroValidacao("Já existe uma categoria com esse nome.")

    def _validar_refs(self, categoria_id, prioridade) -> None:
        if categoria_id is not None:
            self._categoria(categoria_id)
        if prioridade not in PRIORIDADES:
            raise ErroValidacao("Prioridade inválida (use 1, 2 ou 3).")


# ------------------------------------------------------------------ INTERFACE
def ler_int(msg: str, validos=None, vazio_ok: bool = False) -> Optional[int]:
    while True:
        txt = input(msg).strip()
        if not txt and vazio_ok:
            return None
        if txt.isdigit() and (validos is None or int(txt) in validos):
            return int(txt)
        print("  Opção inválida.")


class App:
    def __init__(self, repo: Repositorio):
        self.repo = repo
        self.usuarios = repo.carregar()
        self.auth = ServicoAuth(self.usuarios, self._salvar)
        self.g: Optional[GerenciadorTarefas] = None

    def _salvar(self) -> None:
        self.repo.salvar(self.usuarios)

    @staticmethod
    def _seguro(acao: Callable[[], None]) -> None:
        try:
            acao()
        except ErroValidacao as e:
            print(f"  ! {e}")

    def executar(self) -> None:
        print("=== TO-DO LIST ===")
        while True:
            print("\n1) Entrar   2) Criar conta   0) Sair")
            op = ler_int("> ", {0, 1, 2})
            if op == 0:
                break
            self._seguro(self._entrar if op == 1 else self._cadastrar)
            if self.g:
                self._menu_principal()
                self.g = None
        print("Até logo!")

    # ---- login / cadastro
    def _entrar(self) -> None:
        user = input("Usuário: ")
        senha = getpass.getpass("Senha: ")
        self.g = GerenciadorTarefas(self.auth.login(user, senha), self._salvar)
        print(f"Bem-vindo(a), {self.g.u.username}!")

    def _cadastrar(self) -> None:
        user = input("Novo usuário: ")
        senha = getpass.getpass("Senha (mín. 6): ")
        if senha != getpass.getpass("Confirme a senha: "):
            raise ErroValidacao("As senhas não conferem.")
        self.g = GerenciadorTarefas(self.auth.cadastrar(user, senha), self._salvar)
        print("Conta criada!")

    # ---- menu principal
    def _menu_principal(self) -> None:
        acoes = {1: self._nova, 2: self._listar, 3: self._editar, 4: self._alternar,
                 5: self._excluir, 6: self._desfazer, 7: self._menu_categorias}
        while True:
            print("\n--- MENU ---")
            print("1) Nova tarefa   2) Listar   3) Editar   4) Concluir/reabrir")
            print("5) Excluir   6) Desfazer exclusão   7) Categorias   0) Sair da conta")
            op = ler_int("> ", {0, *acoes})
            if op == 0:
                return
            self._seguro(acoes[op])

    def _mostrar(self, tarefas) -> None:
        if not tarefas:
            print("  (nenhuma tarefa)")
        for t in tarefas:
            marca = "[x]" if t.concluida else "[ ]"
            cat = self.g.nome_categoria(t.categoria_id)
            print(f"  #{t.id:<3} {marca} {t.titulo}  | {PRIORIDADES[t.prioridade]} | {cat}")
            if t.descricao:
                print(f"         {t.descricao}")

    def _escolher_categoria(self, rotulo="Categoria (ENTER = nenhuma): ") -> Optional[int]:
        cats = self.g.listar_categorias()
        if not cats:
            return None
        for c in cats:
            print(f"  {c.id}) {c.nome}")
        return ler_int(rotulo, {c.id for c in cats}, vazio_ok=True)

    def _nova(self) -> None:
        titulo = input("Título: ")
        desc = input("Descrição (opcional): ")
        cat = self._escolher_categoria()
        prio = ler_int("Prioridade 1-Alta 2-Média 3-Baixa (ENTER = Média): ",
                       set(PRIORIDADES), vazio_ok=True) or 2
        t = self.g.criar_tarefa(titulo, desc, cat, prio)
        print(f"  Tarefa #{t.id} criada.")

    def _listar(self) -> None:
        print("Filtro: 1) Todas  2) Pendentes  3) Concluídas  4) Por categoria")
        f = ler_int("> ", {1, 2, 3, 4})
        status = {2: "pendentes", 3: "concluidas"}.get(f)
        cat = self._escolher_categoria("Categoria: ") if f == 4 else None
        self._mostrar(self.g.listar(status, cat))

    def _editar(self) -> None:
        t = self.g.obter(ler_int("ID da tarefa: "))
        print(f"Editando #{t.id} (ENTER mantém o valor atual)")
        titulo = input(f"Título [{t.titulo}]: ").strip() or t.titulo
        desc = input(f"Descrição [{t.descricao}]: ").strip() or t.descricao
        cat = _MANTER
        cats = self.g.listar_categorias()
        if cats:
            for c in cats:
                print(f"  {c.id}) {c.nome}")
            print("  0) Nenhuma")
            n = ler_int("Categoria (ENTER mantém): ", {0, *(c.id for c in cats)}, vazio_ok=True)
            if n is not None:
                cat = n or None
        prio = ler_int("Prioridade 1-Alta 2-Média 3-Baixa (ENTER mantém): ",
                       set(PRIORIDADES), vazio_ok=True)
        self.g.atualizar(t.id, titulo, desc, prio, cat)
        print("  Tarefa atualizada.")

    def _alternar(self) -> None:
        t = self.g.alternar(ler_int("ID da tarefa: "))
        print(f"  #{t.id} agora está {'concluída' if t.concluida else 'pendente'}.")

    def _excluir(self) -> None:
        t = self.g.obter(ler_int("ID da tarefa: "))
        if input(f"Excluir '{t.titulo}'? (s/N): ").strip().lower() == "s":
            self.g.excluir_tarefa(t.id)
            print("  Excluída. (use a opção 6 para desfazer)")

    def _desfazer(self) -> None:
        t = self.g.desfazer_exclusao()
        print(f"  Tarefa #{t.id} '{t.titulo}' restaurada.")

    # ---- categorias
    def _menu_categorias(self) -> None:
        while True:
            print("\n--- CATEGORIAS ---")
            cats = self.g.listar_categorias()
            for c in cats:
                print(f"  {c.id}) {c.nome}")
            if not cats:
                print("  (nenhuma)")
            print("1) Criar   2) Renomear   3) Excluir   0) Voltar")
            op = ler_int("> ", {0, 1, 2, 3})
            if op == 0:
                return
            self._seguro(lambda: self._acao_categoria(op))

    def _acao_categoria(self, op: int) -> None:
        if op == 1:
            c = self.g.criar_categoria(input("Nome: "))
            print(f"  Categoria '{c.nome}' criada.")
            return
        cid = ler_int("ID da categoria: ")
        if op == 2:
            self.g.renomear_categoria(cid, input("Novo nome: "))
            print("  Categoria renomeada.")
        else:
            n = self.g.excluir_categoria(cid)
            print(f"  Categoria excluída ({n} tarefa(s) ficaram sem categoria).")


if __name__ == "__main__":
    try:
        App(RepositorioJSON(ARQUIVO_DADOS)).executar()
    except (KeyboardInterrupt, EOFError):
        print("\nEncerrado.")
