// FlexWeek_tmp_tmpc_tfdj_3_ex2.dfy

function abs(a: int): nat
{
  if a < 0 then
    -a
  else
    a
}

method aba(a: array<int>) returns (b: array<int>)
  ensures a.Length == b.Length
  ensures forall x :: 0 <= x < b.Length ==> b[x] == abs(a[x])
{
  b := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: 0 <= x < i ==> b[x] == abs(a[x])
  {
    break;
    if a[i] < 0 {
      b[i] := -a[i];
    } else {
      b[i] := a[i];
    }
    i := i + 1;
  }
}

method Main()
{
  var a := new int[] [1, -2, -2, 1];
  var b := aba(a);
  assert b[..] == [1, 2, 2, 1];
}
