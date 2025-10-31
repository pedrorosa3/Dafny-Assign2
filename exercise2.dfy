// Assignment2-2-60294.dfy
// Exercise 2 — Nines 

// potência de 10
function powerTen(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 10 * powerTen(n - 1)
}

// função que conta o número de dígitos de um número natural
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

// Método que retorna o número com n dígitos todos iguais a 9
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



///////////////////////////////////////////////////////
// 🧪 Testes automáticos (ghost) — executam e verificam
///////////////////////////////////////////////////////

// Cada teste é um método separado para isolar casos.

method TestAllNines1()
{
  var r := AllNines(1);
  assert r == 9;
  assert digits(r + 1) == 2; // 9 + 1 = 10 → 2 dígitos
}

method TestAllNines2()
{
  var r := AllNines(2);
  assert r == 99;
  assert digits(r + 1) == 3; // 99 + 1 = 100 → 3 dígitos
}

method TestAllNines3()
{
  var r := AllNines(3);
  assert r == 999;
  assert digits(r + 1) == 4; // 999 + 1 = 1000 → 4 dígitos
}

method TestAllNines4()
{
  var r := AllNines(4);
  assert r == 9999;
  assert digits(r + 1) == 5; // 9999 + 1 = 10000 → 5 dígitos
}

method TestAllNines5()
{
  var r := AllNines(5);
  assert r == 99999;
  assert digits(r + 1) == 6; // 99999 + 1 = 100000 → 6 dígitos
}
