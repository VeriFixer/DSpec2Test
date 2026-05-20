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
    if InSeq(b, a[i]) <==> a[i] !in res {
      res := res + [a[i]];
    }
  }
  result := res;
}

method {:test} Test0() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i, j | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
