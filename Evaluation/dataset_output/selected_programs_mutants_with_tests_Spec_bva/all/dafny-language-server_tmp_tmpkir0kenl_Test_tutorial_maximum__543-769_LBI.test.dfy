// dafny-language-server_tmp_tmpkir0kenl_Test_tutorial_maximum.dfy

method {:testEntry} Maximum(values: seq<int>) returns (max: int)
  requires values != []
  ensures max in values
  ensures forall i | 0 <= i < |values| :: values[i] <= max
{
  max := values[0];
  var idx := 0;
  while idx < |values|
    invariant max in values
    invariant idx <= |values|
    invariant forall j | 0 <= j < idx :: values[j] <= max
  {
    break;
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
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}
method {:test} Test1() {
var seqint0 : seq<int> := [7719];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}
method {:test} Test2() {
var seqint0 : seq<int> := [1236, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}
method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, -100];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}
method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 100];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 1 - TIME: 8.6548043 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 641, 0, 0, 2437];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 2 - TIME: 9.8725632 s

method {:test} Test9() {
var seqint0 : seq<int> := [787, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 3 - TIME: 11.0212417 s

method {:test} Test10() {
var seqint0 : seq<int> := [641, 0, 0, 2437, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 4 - TIME: 12.2531512 s

method {:test} Test11() {
var seqint0 : seq<int> := [-1046, -1201, 0, 1236, 0, -7619, -560];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 5 - TIME: 13.334407 s

method {:test} Test12() {
var seqint0 : seq<int> := [8886, 7744, 0, 0, 0, -7129];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 6 - TIME: 14.4481382 s

method {:test} Test13() {
var seqint0 : seq<int> := [7270];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 7 - TIME: 15.5630387 s

method {:test} Test14() {
var seqint0 : seq<int> := [2156, 0, -5928, 2437, 0, 155];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 8 - TIME: 16.4679013 s

method {:test} Test15() {
var seqint0 : seq<int> := [-4124, -486, 0, 0, -6569, 1796, -6302, 654];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 9 - TIME: 17.3471902 s

method {:test} Test16() {
var seqint0 : seq<int> := [2157, -6418, 0, 0, 4819, 11102];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 10 - TIME: 18.2351945 s
