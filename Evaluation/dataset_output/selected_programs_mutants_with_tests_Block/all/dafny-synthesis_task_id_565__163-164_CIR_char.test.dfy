// dafny-synthesis_task_id_565.dfy

method {:testEntry} SplitStringIntoChars(s: string) returns (v: seq<char>)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
{
  v := ['a', 'b', 'c'];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant forall k :: 0 <= k < i ==> v[k] == s[k]
  {
    v := v + [s[i]];
  }
}


method {:test} Test0() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}

// REPEAT 1 - TIME: 2.8556648 s

method {:test} Test1() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}

// REPEAT 2 - TIME: 3.9264903 s

method {:test} Test2() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}

// REPEAT 3 - TIME: 4.9516422 s

method {:test} Test3() {
var r0 := SplitStringIntoChars("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[i];
}

// REPEAT 4 - TIME: 5.8464301 s

method {:test} Test4() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}

// REPEAT 5 - TIME: 6.7448846 s

method {:test} Test5() {
var r0 := SplitStringIntoChars("\0aaaaaaaaaaaaaaa\U{0002}");
expect |r0| == |"\0aaaaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaa\U{0002}"| ==> r0[i] == "\0aaaaaaaaaaaaaaa\U{0002}"[i];
}

// REPEAT 6 - TIME: 7.5606335 s

method {:test} Test6() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}

// REPEAT 7 - TIME: 8.3069653 s

method {:test} Test7() {
var r0 := SplitStringIntoChars("\0aaaaaaaaaaaaaaa\U{0002}");
expect |r0| == |"\0aaaaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaa\U{0002}"| ==> r0[i] == "\0aaaaaaaaaaaaaaa\U{0002}"[i];
}

// REPEAT 8 - TIME: 8.936783 s

method {:test} Test8() {
var r0 := SplitStringIntoChars("\0aaaaaaaaaaaaaaa\U{0002}");
expect |r0| == |"\0aaaaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaa\U{0002}"| ==> r0[i] == "\0aaaaaaaaaaaaaaa\U{0002}"[i];
}

// REPEAT 9 - TIME: 9.5365131 s

method {:test} Test9() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}

// REPEAT 10 - TIME: 10.0424901 s
