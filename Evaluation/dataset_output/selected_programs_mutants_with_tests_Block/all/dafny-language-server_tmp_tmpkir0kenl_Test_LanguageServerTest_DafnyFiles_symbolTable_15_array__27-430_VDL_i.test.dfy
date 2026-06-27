// dafny-language-server_tmp_tmpkir0kenl_Test_LanguageServerTest_DafnyFiles_symbolTable_15_array.dfy

method {:testEntry} Main()
{
  var s := [1, 3, 4, 5];
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

// REPEAT 1 - TIME: 2.8565343 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 2 - TIME: 3.5790489 s

method {:test} Test3() {
var seqint0 : seq<int> := [2, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 3 - TIME: 4.3165972 s

method {:test} Test4() {
var seqint0 : seq<int> := [3, 0, 5];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 4 - TIME: 4.9233024 s

method {:test} Test5() {
var seqint0 : seq<int> := [4, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 5 - TIME: 5.6483614 s

method {:test} Test6() {
var seqint0 : seq<int> := [6, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 6 - TIME: 6.3177995 s

method {:test} Test7() {
var seqint0 : seq<int> := [11, 0, 0, 9, 0, 7];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 7 - TIME: 7.1067215 s

method {:test} Test8() {
var seqint0 : seq<int> := [8, 0, 12, 14];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 8 - TIME: 7.8834814 s

method {:test} Test9() {
var seqint0 : seq<int> := [10, 0, 0, 15];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 9 - TIME: 8.4922555 s

method {:test} Test10() {
var seqint0 : seq<int> := [17, 0, 0, 0, 13];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 10 - TIME: 9.1103498 s
