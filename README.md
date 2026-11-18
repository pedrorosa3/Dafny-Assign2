<div align="center">

# 🛡️ Software Fiável — Assignment 2
### Design by Contract com Dafny

![Dafny](https://img.shields.io/badge/Dafny-4.x-6A1B9A?style=for-the-badge)
![Z3](https://img.shields.io/badge/SMT-Z3-1565C0?style=for-the-badge)
![FCUL](https://img.shields.io/badge/FCUL-MEI%202025%2F2026-2E7D32?style=for-the-badge)

**Autor:** Pedro Rosa (n.º 60294)  
**Data:** Novembro de 2025  
**Instituição:** Faculdade de Ciências da Universidade de Lisboa  
**Curso:** Mestrado em Engenharia Informática — Software Fiável

</div>

---

## 📌 Sobre o projeto

Este repositório contém a resolução do segundo trabalho prático da unidade curricular de **Software Fiável**. O objetivo é a **verificação formal** de algoritmos e estruturas de dados através de **Design by Contract**: pré-condições, pós-condições, invariantes de ciclo e invariantes de classe, verificadas automaticamente pelo **Dafny** (com o solver SMT **Z3** por trás).

---

## 🧩 Exercícios

| # | Exercício | Ficheiro | Resumo |
|:-:|-----------|----------|--------|
| 1 | **Number Trick** | [`Assignment2-1-60294.pdf`](Assignment2-1-60294.pdf) | Cálculo analítico de $WLP(Trick,\ y \ge x)$ e condições lógicas para verificação em Z3. |
| 2 | **Nines** | [`Assignment2-2-60294.dfy`](Assignment2-2-60294.dfy) | Método `AllNines` que calcula o número com $n$ dígitos iguais a 9, com contratos apoiados em $powerTen(n) = 10^n$ e `digits`. |
| 3 | **Minimum Distance in 2D** | [`Assignment2-3-60294.dfy`](Assignment2-3-60294.dfy) | Método `MinDistance`: diferença absoluta mínima entre elementos de dois arrays ordenados, com invariantes de ciclo que provam a travessia. |
| 4 | **Minesweeper** | [`Assignment2-4-60294.dfy`](Assignment2-4-60294.dfy) | O jogo Minesweeper como *Abstract Data Type*: invariante de classe, abrir células, colocar/retirar bandeiras e condições de vitória/derrota. |

📄 O enunciado completo está em [`assignment2.pdf`](assignment2.pdf).

---

## 📂 Estrutura

```
Dafny-Assign2/
├── assignment2.pdf            # Enunciado do trabalho
├── Assignment2-1-60294.pdf    # Ex. 1 — respostas teóricas e expressões Z3
├── Assignment2-2-60294.dfy    # Ex. 2 — Nines
├── Assignment2-3-60294.dfy    # Ex. 3 — Minimum Distance in 2D
├── Assignment2-4-60294.dfy    # Ex. 4 — Minesweeper
└── README.md
```

---

## ⚙️ Requisitos

- [**Dafny 4.x**](https://github.com/dafny-lang/dafny/releases) (inclui o Z3) — testado com **Dafny 4.11.0**
- Para **executar** o exercício 4, um destes:
  - [**.NET 8 SDK**](https://dotnet.microsoft.com/download) (alvo C#, o padrão), ou
  - [**Python 3**](https://www.python.org/downloads/) (alvo `--target:py`)
- *(Opcional)* **VS Code** com a extensão [Dafny](https://marketplace.visualstudio.com/items?itemName=dafny-lang.ide-vscode), que instala o Dafny automaticamente e verifica o código em tempo real

---

## ▶️ Como executar

### 1. Clonar o repositório

```bash
git clone https://github.com/pedrorosa3/Dafny-Assign2.git
cd Dafny-Assign2
```

### 2. Verificar os programas

Cada ficheiro pode ser verificado individualmente. Os métodos de teste (`TestAllNines*`, `Test*_...`, `test*`) são verificados **estaticamente**, por isso uma verificação sem erros significa que os testes passam.

```bash
dafny verify Assignment2-2-60294.dfy
dafny verify Assignment2-3-60294.dfy
dafny verify Assignment2-4-60294.dfy
```

Resultado esperado:

| Ficheiro | Resultado |
|----------|-----------|
| `Assignment2-2-60294.dfy` | ✅ 9 verified, 0 errors |
| `Assignment2-3-60294.dfy` | ✅ 9 verified, 0 errors |
| `Assignment2-4-60294.dfy` | ✅ 25 verified, 0 errors |

> ℹ️ O Dafny pode imprimir mensagens `Prover error: Could not parse any models` vindas do Z3. São inofensivas e não afetam o resultado da verificação.

### 3. Executar o Minesweeper

O exercício 4 tem um método `Main` que simula uma sequência de jogadas num tabuleiro 3×3 com 2 minas e imprime o tabuleiro a cada passo:

```bash
dafny run Assignment2-4-60294.dfy                # requer .NET SDK
dafny run --target:py Assignment2-4-60294.dfy    # alternativa com Python
```

Saída final esperada:

```
Action: o on position (1, 3)
---
**1
221
000
---
Congratulations! You've won the game!
```

> 💡 Para simular um jogo perdido, troque `inputPos` pela sequência alternativa que está comentada no `Main`.

### 4. No VS Code

Abra a pasta no VS Code com a extensão Dafny instalada. A verificação corre automaticamente ao guardar, e os erros aparecem sublinhados no editor.

---

<div align="center">

Feito por **Pedro Rosa** · FCUL · Novembro de 2025

</div>
