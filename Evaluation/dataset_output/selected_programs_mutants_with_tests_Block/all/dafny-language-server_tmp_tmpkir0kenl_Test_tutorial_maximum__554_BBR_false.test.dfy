// dafny-language-server_tmp_tmpkir0kenl_Test_tutorial_maximum.dfy

method {:testEntry} Maximum(values: seq<int>) returns (max: int)
  requires values != []
  ensures max in values
  ensures forall i | 0 <= i < |values| :: values[i] <= max
{
  max := values[0];
  var idx := 0;
  while false
    invariant max in values
    invariant idx <= |values|
    invariant forall j | 0 <= j < idx :: values[j] <= max
  {
    if values[idx] > max {
      max := values[idx];
    }
    idx := idx + 1;
  }
}

lemma MaximumIsUnique(values: seq<int>, m1: int, m2: int)
  requires m1 in values && forall i | 0 <= i < |values| :: values[i] <= m1
  requires m2 in values && forall i | 0 <= i < |values| :: values[i] <= m2
  ensures m1 == m2
{
}


method {:test} Test0() {
var seqint0 : seq<int> := [8882];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}
method {:test} Test1() {
var seqint0 : seq<int> := [8883, 8882];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 1 - TIME: 2.7488637 s

method {:test} Test2() {
var seqint0 : seq<int> := [8856, 8855];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 2 - TIME: 3.506276 s

method {:test} Test3() {
var seqint0 : seq<int> := [2438, 0, 0, 0, 0, 0, 0, 0, 2437, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 3 - TIME: 4.4949199 s

method {:test} Test4() {
var seqint0 : seq<int> := [1797, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796, 0, 0, 4, 0, 0, 0, 0, 8, 0, 6];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 4 - TIME: 5.3548175 s

method {:test} Test5() {
var seqint0 : seq<int> := [1797, 0, 0, 5, 0, 0, 0, 1796];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 5 - TIME: 6.2375962 s

method {:test} Test6() {
var seqint0 : seq<int> := [-684, 9, 0, 5853, 0, 1598, 0, 0, 0, 0, 11];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}
method {:test} Test7() {
var seqint0 : seq<int> := [623, 622, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 6 - TIME: 7.7612221 s

method {:test} Test8() {
var seqint0 : seq<int> := [8856, 8855, 7, 12];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 7 - TIME: 8.7122412 s

method {:test} Test9() {
var seqint0 : seq<int> := [8366, 10, 0, 8365, 14];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 8 - TIME: 9.4990987 s

method {:test} Test10() {
var seqint0 : seq<int> := [-8765, 13, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8316, 18, 0, 0, 0, 0, 0, 20];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}
method {:test} Test11() {
var seqint0 : seq<int> := [1338, 1337];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 9 - TIME: 10.6152632 s

method {:test} Test12() {
var seqint0 : seq<int> := [1237, 0, 0, 1236, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 10 - TIME: 11.4359305 s
