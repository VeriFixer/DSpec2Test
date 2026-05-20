predicate InSeq(a: seq<int>, x: int)
{
    exists i :: 0 <= i < |a| && a[i] == x
}

method {:testEntry} SharedElements(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    // All elements in the output are in both a and b
    ensures forall x | x in result :: (InSeq(a, x) && InSeq(b, x))
    // The elements in the output are all different
    ensures forall i, j | 0 <= i < j < |result| :: result[i] != result[j]
{
    var res: seq<int> := [];
    for i := 0 to |a|
        invariant 0 <= i <= |a|
        invariant forall x :: x in res ==> InSeq(a, x) && InSeq(b, x)
        invariant forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
    {
        if InSeq(b, a[i]) && a[i] !in res
        {
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
method {:test} Test5() {
var seqint0 : seq<int> := [3];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test6() {
var seqint0 : seq<int> := [5, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test7() {
var seqint0 : seq<int> := [3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test8() {
var seqint0 : seq<int> := [3, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test9() {
var seqint0 : seq<int> := [3, 0, 0, 42, 0, 0, 5];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test10() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 8, 0, 14];
var seqint1 : seq<int> := [18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test11() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test13() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test14() {
var seqint0 : seq<int> := [11, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 176, 0, 0, 0, 0, 0, 178, 0, 0, 0, 0, 0, 0, 0, 0, 0, 181, 179, 175, 0, 0, 0, 0, 183];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test15() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test16() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test17() {
var seqint0 : seq<int> := [9, 0, 4, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test18() {
var seqint0 : seq<int> := [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
method {:test} Test19() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 53];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 367, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [];
var r0 := SharedElements(seqint0, seqint1);
expect forall x: int {:trigger InSeq(seqint1, x)} {:trigger InSeq(seqint0, x)} {:trigger x in r0} | x in r0 :: InSeq(seqint0, x) && InSeq(seqint1, x);
expect forall i: int, j: int {:trigger r0[j], r0[i]} | 0 <= i < j < |r0| :: r0[i] != r0[j];
}
