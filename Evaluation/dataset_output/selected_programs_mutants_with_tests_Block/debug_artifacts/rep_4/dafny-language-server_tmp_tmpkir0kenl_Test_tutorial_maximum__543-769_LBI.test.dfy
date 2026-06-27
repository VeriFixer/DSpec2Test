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

method {:test} Test4() {
var seqint0 : seq<int> := [1797, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796, 0, 0, 4, 0, 0, 0, 0, 8, 0, 6];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Maximum(seqint0);
expect r0 in seqint0;
expect forall i | 0 <= i < |seqint0| :: seqint0[i] <= r0;
}

// REPEAT 4 - TIME: 5.3548175 s
