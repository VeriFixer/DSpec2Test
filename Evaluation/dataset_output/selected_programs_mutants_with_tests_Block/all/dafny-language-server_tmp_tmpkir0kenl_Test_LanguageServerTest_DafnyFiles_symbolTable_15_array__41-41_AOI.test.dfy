// dafny-language-server_tmp_tmpkir0kenl_Test_LanguageServerTest_DafnyFiles_symbolTable_15_array.dfy

method {:testEntry} Main()
{
  var i := -2;
  var s := [1, i, 3, 4, 5];
  print |s|;
  assert s[|s| - 1] == 5;
  assert s[|s| - 1 .. |s|] == [5];
  assert s[1..] == [2, 3, 4, 5];
  assert s[..|s| - 1] == [1, 2, 3, 4];
  assert s == s[0..] == s[..|s|] == s[0 .. |s|] == s[..];
}

method {:testEntry} foo(s: seq<int>)
  requires |s| > 1
{
  print s[1];
}


method {:test} Test0() {
Main();
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 1 - TIME: 2.5528178 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 2 - TIME: 3.6141023 s

method {:test} Test3() {
var seqint0 : seq<int> := [2, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 3 - TIME: 4.4696212 s

method {:test} Test4() {
var seqint0 : seq<int> := [3, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 4 - TIME: 5.1021877 s

method {:test} Test5() {
var seqint0 : seq<int> := [4, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 5 - TIME: 5.8506381 s

method {:test} Test6() {
var seqint0 : seq<int> := [5, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 6 - TIME: 6.5312202 s

method {:test} Test7() {
var seqint0 : seq<int> := [6, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 7 - TIME: 7.3022844 s

method {:test} Test8() {
var seqint0 : seq<int> := [7, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 8 - TIME: 8.0042908 s

method {:test} Test9() {
var seqint0 : seq<int> := [10, 0, 8, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 9 - TIME: 8.6902927 s

method {:test} Test10() {
var seqint0 : seq<int> := [9, 0, 12, 14];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 10 - TIME: 9.2030099 s
