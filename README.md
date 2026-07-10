# Software Fiável - Assignment 2 (Design by Contract)

**Instituição:** Faculdade de Ciências da Universidade de Lisboa (FCUL)
**Curso:** Mestrado em Engenharia de Informática (2025/2026)
**Autor:** Pedro Rosa (60294)

## 📌 Descrição do Projeto
Este repositório contém a resolução do segundo trabalho prático da disciplina de Software Fiável. O foco principal da avaliação é a verificação formal de algoritmos e estruturas de dados através da aplicação de metodologias de **Design by Contract**, utilizando a linguagem e o verificador **Dafny**.

## 📂 Estrutura e Exercícios
O projeto está dividido em quatro secções independentes:

* **1. Number Trick:** Análise matemática de um programa simples para manipulação de inteiros. Inclui o cálculo analítico da fórmula $WLP(Trick, y \ge x)$ e a formulação de condições lógicas para verificação automática via Z3.
* **2. Nines:** Implementação do método `AllNines`, concebido para calcular um número composto por $n$ dígitos iguais a 9. O desenvolvimento inclui a definição de contratos precisos, suportados pela função auxiliar $powerTen(n) = 10^n$, e garantias formais sobre a quantidade de dígitos gerados.
* **3. Minimum Distance in 2D:** Verificação do método `MinDistance`, um algoritmo que procura a diferença absoluta mínima entre elementos de dois arrays ordenados. A solução documenta invariantes de ciclo rigorosas que provam a correção da travessia dos arrays.
* **4. Minesweeper:** Modelação do jogo Minesweeper como um *Abstract Data Type* (ADT). A implementação foca-se na construção de uma invariante de classe sólida e na especificação baseada em propriedades para operações de estado como a abertura de células, colocação de bandeiras e verificação de condições de vitória ou derrota.

## 📦 Ficheiros Submetidos
Em conformidade com as regras da avaliação, o repositório contém os ficheiros correspondentes a cada exercício, identificados pelo número de aluno:

* `Assignment2-1-60294.pdf` (Respostas teóricas e expressões Z3 do Exercício 1)
* `Assignment2-2-60294.dfy` (Código fonte e contratos do Exercício 2)
* `Assignment2-3-60294.dfy` (Código fonte e contratos do Exercício 3)
* `Assignment2-4-60294.dfy` (Código fonte e contratos do Exercício 4)


