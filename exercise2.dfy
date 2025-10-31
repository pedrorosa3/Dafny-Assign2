// Assignment2-2-corrigido.dfy
// Exercise 2 — Nines (correção: adicionada lemma para digits(powerTen(n)) == n+1)

function powerTen(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 10 * powerTen(n - 1)
}

function digits(num: nat): nat
  decreases num
{
  if num < 10 then 1 else 1 + digits(num / 10)
}

// Lemma: prova por indução que digits(powerTen(n)) == n + 1
lemma digits_powerTen(n: nat)
  ensures digits(powerTen(n)) == n + 1
  decreases n
{
  if n == 0 {
    // powerTen(0) = 1 e digits(1) = 1
  } else {
    // passo indutivo: assumimos para n-1
    digits_powerTen(n - 1);

    // facts usados a seguir
    assert powerTen(n) == 10 * powerTen(n - 1);
    // para n>=1, powerTen(n) >= 10, logo aplicamos a definição de digits
    assert digits(powerTen(n)) == 1 + digits(powerTen(n) / 10);
    assert powerTen(n) / 10 == powerTen(n - 1); // divisão inteira compatível com multiplicação por 10
    assert digits(powerTen(n)) == 1 + digits(powerTen(n - 1));
    // aplicar o caso indutivo
    assert digits(powerTen(n - 1)) == (n - 1) + 1;
    assert digits(powerTen(n)) == 1 + ((n - 1) + 1);
    assert digits(powerTen(n)) == n + 1;
  }
}

method AllNines(n: nat) returns (r: nat)
  requires n > 0
  ensures r == powerTen(n) - 1
{
  var i := 1;
  r := 9;

  while i < n
    invariant 1 <= i && i <= n
    invariant r == powerTen(i) - 1
    decreases n - i
  {
    r := r * 10 + 9;
    i := i + 1;
  }

  // Pela invariante, i == n e r == powerTen(n) - 1
  assert r == powerTen(n) - 1;

  // r + 1 == powerTen(n)
  assert r + 1 == powerTen(n);

  // Usamos a lemma para saber digits(powerTen(n)) == n+1
  digits_powerTen(n);

  // Agora a asserção final é imediata
  assert digits(r + 1) == n + 1;
}
