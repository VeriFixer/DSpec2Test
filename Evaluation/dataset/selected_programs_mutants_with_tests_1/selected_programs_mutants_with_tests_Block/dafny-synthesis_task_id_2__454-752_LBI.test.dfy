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
    break;
    if InSeq(b, a[i]) && a[i] !in res {
      res := res + [a[i]];
    }
  }
  result := res;
}

method {:test} Test0() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i, j | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i, j | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i, j | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i, j | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
