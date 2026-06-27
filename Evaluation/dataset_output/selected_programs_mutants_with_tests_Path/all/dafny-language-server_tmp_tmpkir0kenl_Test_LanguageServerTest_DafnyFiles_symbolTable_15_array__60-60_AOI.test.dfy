// dafny-language-server_tmp_tmpkir0kenl_Test_LanguageServerTest_DafnyFiles_symbolTable_15_array.dfy

method {:testEntry} Main()
{
  var i := 2;
  var s := [1, -i, 3, 4, 5];
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

// REPEAT 1 - TIME: 7.0454522 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 2 - TIME: 7.9478029 s

method {:test} Test3() {
var seqint0 : seq<int> := [2, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 3 - TIME: 8.7109547 s

method {:test} Test4() {
var seqint0 : seq<int> := [3, 0, 5];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 4 - TIME: 9.4839229 s

method {:test} Test5() {
var seqint0 : seq<int> := [4, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 5 - TIME: 10.320243 s

method {:test} Test6() {
var seqint0 : seq<int> := [6, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 6 - TIME: 10.9893957 s

method {:test} Test7() {
var seqint0 : seq<int> := [11, 0, 0, 9, 0, 7];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 7 - TIME: 11.7101455 s

method {:test} Test8() {
var seqint0 : seq<int> := [8, 0, 12, 14];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 8 - TIME: 12.3367787 s

method {:test} Test9() {
var seqint0 : seq<int> := [10, 0, 0, 15];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 9 - TIME: 12.9575367 s

method {:test} Test10() {
var seqint0 : seq<int> := [17, 0, 0, 0, 13];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 10 - TIME: 13.6263344 s
