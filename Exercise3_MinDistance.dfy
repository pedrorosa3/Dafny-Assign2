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
      //decreases a.Length - i + b.Length - j
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
        if i + 1 >= a.Length { break; }
        i := i + 1;
        assert i < a.Length;
      } else {
        if j + 1 >= b.Length { break; }
        j := j + 1;
        assert j < b.Length;
      }
      assert 0 <= iMin < a.Length;
      assert 0 <= jMin < b.Length;
      assert d <= Abs(a[iMin] - b[jMin]);
      assert 0 <= i < a.Length;
      assert 0 <= j < b.Length;
      //assert (i < a.Length && j < b.Length) ==> d <= Abs(a[i] - b[j]);
      

    }
  }
}


