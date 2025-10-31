module Assignment2_Ex3 {

  // Pedro Rosa - Exercise 3: Minimum Distance in 2D
  // Versão verificada (one while, iMin/jMin guardados) corrigida para evitar index out of range

  function Abs(x: int): nat {
    if x >= 0 then x else -x
  }

  method MinDistance(a: array<int>, b: array<int>)
    returns (d: nat, iMin: int, jMin: int)
    requires a != null && b != null
    requires a.Length > 0 && b.Length > 0
    requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i+1]
    requires forall j :: 0 <= j < b.Length - 1 ==> b[j] <= b[j+1]
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
      invariant d <= Abs(a[iMin] - b[jMin])
      


      // proteger o acesso com a condição de validade dos índices
      invariant (i < a.Length && j < b.Length) ==> d <= Abs(a[i] - b[j])
    {
      var cur := Abs(a[i] - b[j]);
      assert d <= Abs(a[i] - b[j]);
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
      assert 0 <= iMin < a.Length;
      assert 0 <= jMin < b.Length;
      assert d <= Abs(a[iMin] - b[jMin]);
      assert 0 <= i < a.Length;
      assert 0 <= j < b.Length;
      assert (i < a.Length && j < b.Length) ==> d <= Abs(a[i] - b[j]);
      

    }
  }
}


