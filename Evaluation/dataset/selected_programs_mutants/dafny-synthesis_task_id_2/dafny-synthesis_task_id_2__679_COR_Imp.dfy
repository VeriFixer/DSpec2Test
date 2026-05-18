// dafny-synthesis_task_id_2.dfy

predicate InSeq(a: seq<int>, x: int)
{
  exists i :: 
    0 <= i < |a| &&
    a[i] == x
}

method {:testEntry} SharedElements(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  ensures forall x | x in result :: InSeq(a, x) && InSeq(b, x)
  ensures forall i, j | 0 <= i < j < |result| :: result[i] != result[j]
{
  var res: seq<int> := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant forall x :: x in res ==> InSeq(a, x) && InSeq(b, x)
    invariant forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  {
    if InSeq(b, a[i]) ==> a[i] !in res {
      res := res + [a[i]];
    }
  }
  result := res;
}
