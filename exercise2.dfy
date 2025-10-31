// Assignment2-2-60294.dfy
// Exercise 2 — Nines
// Implementação em Dafny com contratos, invariantes e funções auxiliares.

// powerTen: função que calcula 10^n
function powerTen(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 10 * powerTen(n - 1)
}

// digits: função que retorna o número de dígitos de um número natural
function digits(num: nat): nat
  decreases num
{
  if num < 10 then 1 else 1 + digits(num / 10)
}

// Método AllNines: retorna r = número com n dígitos todos a 9.
// Exemplo: n = 3 -> r = 999 = 10^3 - 1
method AllNines(n: nat) returns (r: nat)
  requires n > 0
  ensures r == powerTen(n) - 1
{
  var i := 1;
  r := 9;

  // Invariante: após k iterações (i == k), r == 10^i - 1
  // Além disso, mantemos que 1 <= i <= n durante o loop.
  // Decreases para provar terminação do while.
  while i < n
    invariant 1 <= i && i <= n
    invariant r == powerTen(i) - 1
    decreases n - i
  {
    // Atualização que preserva a invariante:
    // Se r = 10^i - 1 então r*10 + 9 = 10^(i+1) - 1
    r := r * 10 + 9;
    i := i + 1;
  }

  // Ao sair do ciclo, i == n e pela invariante r == powerTen(n) - 1.
  assert r == powerTen(n) - 1;

  // Alínea 3: verificar a propriedade sobre digits
  // r + 1 == 10^n, e digits(10^n) == n+1 (por definição de digits),
  // logo digits(r + 1) == n + 1.
  assert digits(r + 1) == n + 1;
}
