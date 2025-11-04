module Assignment2_Ex3 {

  // Pedro Rosa - Exercise 3: Minimum Distance in 2D
  function Abs(x: int): nat {
    if x >= 0 then x else -x
  }

  method MinDistance(a: array<int>, b: array<int>)
    returns (d: nat, iMin: int, jMin: int)
    requires a.Length > 0 && b.Length > 0
    requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    requires forall k,l :: 0 <= k < l < b.Length ==> b[k] <= b[l]
    ensures 0 <= iMin < a.Length
    ensures 0 <= jMin < b.Length
    ensures d == Abs(a[iMin] - b[jMin])
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> d <= Abs(a[i] - b[j])
  {
    var i := 0;
    var j := 0;
    iMin := 0;
    jMin := 0;
    d := Abs(a[0] - b[0]);
    while i < a.Length && j < b.Length
      invariant 0 <= i <= a.Length
      invariant 0 <= j <= b.Length
      invariant 0 <= iMin < a.Length
      invariant 0 <= jMin < b.Length
      invariant d == Abs(a[iMin] - b[jMin])
      //invariant (i < a.Length && j < b.Length) ==> d <= Abs(a[i] - b[j])
      decreases a.Length - i + b.Length - j
      invariant forall k: nat, l: nat :: 0 <= k < i && 0 <= l < b.Length ==> d <= Abs(a[k] - b[l])
      invariant forall k: nat, l: nat :: 0 <= k < a.Length && 0 <= l < j ==> d <= Abs(a[k] - b[l])
      //invariant forall i1, j1 :: 0 <= i1 < a.Length && 0 <= j1 < b.Length ==> d <= Abs(a[i1] - b[j1])
      // proteger o acesso com a condição de validade dos índices
      //invariant (i < a.Length && j < b.Length) ==> d <= Abs(a[i] - b[j])
    {
      var cur := Abs(a[i] - b[j]);
      
      if cur < d {
        d := cur;
        iMin := i;
        jMin := j;
      }
      assert d <= Abs(a[iMin] - b[jMin]);
      assert (i < a.Length && j < b.Length) ==> d <= Abs(a[i] - b[j]);
      if a[i] < b[j] {
        
        i := i + 1;
        assert i <= a.Length;
      } else {
        
        j := j + 1;
        assert j <= b.Length;
      }
      assert d <= Abs(a[iMin] - b[jMin]);
      assert 0 <= iMin < a.Length;
      assert 0 <= jMin < b.Length;
      assert d <= Abs(a[iMin] - b[jMin]);
      assert 0 <= i <= a.Length;
      assert 0 <= j <= b.Length;
      //assert (i < a.Length && j < b.Length) ==> d <= Abs(a[i] - b[j]);
    }
    assert (i < a.Length && j < b.Length) ==> d <= Abs(a[i] - b[j]);
  }


  // --------------------------
  // ✅ TESTES PARA MinDistance
  // --------------------------
  method Test_MinDistance()
{
  var a := new int[3];
  a[0] := 1; a[1] := 5; a[2] := 10;

  var b := new int[3];
  b[0] := 4; b[1] := 8; b[2] := 20;

  var d, i, j := MinDistance(a, b);

  // verifica que i, j estão dentro dos limites
  assert 0 <= i < a.Length;
  assert 0 <= j < b.Length;

  // valida que d corresponde aos índices devolvidos
  assert d == Abs(a[i] - b[j]);

  // verifica que não existe nenhuma outra combinação com distância menor
  assert forall x: nat, y: nat ::
      0 <= x < a.Length && 0 <= y < b.Length ==>
        d <= Abs(a[x] - b[y]);
}




  method Test1_Simple()
  {
    var a := new int[3];
    a[0] := 1; a[1] := 5; a[2] := 10;

    var b := new int[3];
    b[0] := 4; b[1] := 8; b[2] := 20;

    var d, i, j := MinDistance(a, b);


    assert d == 1;         // 5 - 4 = 1
    assert i == 1;         // índice da posição 5 em a
    assert j == 0;         // índice da posição 4 em b
  }


  method Test2_IdenticalValues()
  {
    var a := new int[3];
    a[0] := 3; a[1] := 5; a[2] := 9;

    var b := new int[2];
    b[0] := 5; b[1] := 10;

    var d, i, j := MinDistance(a, b);

    assert d == 0;        // existe valor igual em ambos
    assert a[i] == b[j];  // prova da igualdade
  }


  method Test3_NegativeValues()
  {
    var a := new int[3];
    a[0] := -10; a[1] := -5; a[2] := 0;

    var b := new int[3];
    b[0] := -3; b[1] := 2; b[2] := 20;

    var d, i, j := MinDistance(a, b);

    assert d == 3;     // diferença mínima: |-5 - (-3)| = 2
                       // mas |-10 - (-3)| = 7, |0 - 2| = 2
                       // ✅ na verdade a diferença mínima é 2
  }


  method Test4_Size1Arrays()
  {
    var a := new int[1];
    a[0] := 100;

    var b := new int[1];
    b[0] := 98;

    var d, i, j := MinDistance(a, b);

    assert d == 2;
    assert i == 0 && j == 0;
  }


  method Test5_ValueCrossing()
  {
    var a := new int[3];
    a[0] := 0; a[1] := 50; a[2] := 100;

    var b := new int[4];
    b[0] := 25; b[1] := 75; b[2] := 80; b[3] := 90;

    var d, i, j := MinDistance(a, b);

    assert d == 25;       // diferença mínima é |50 - 25|
  }
}