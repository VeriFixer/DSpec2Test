// dafny-synthesis_task_id_565.dfy

method {:testEntry} SplitStringIntoChars(s: string) returns (v: seq<char>)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
{
  v := [];
  for i := 1 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant forall k :: 0 <= k < i ==> v[k] == s[k]
  {
    v := v + [s[i]];
  }
}


method {:testEntry} SplitStringIntoChars(s: string) returns (v: seq<char>)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
{
    v := [];
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant |v| == i
        invariant forall k :: 0 <= k < i ==> v[k] == s[k]
    {
        v := v + [s[i]];
    }
}

method {:test} Test0() {
var r0 := SplitStringIntoChars("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> r0[i] == "a"[i];
}

// REPEAT 1 - TIME: 11.0774587 s

method {:test} Test1() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}

// REPEAT 2 - TIME: 18.0239245 s

method {:test} Test2() {
var r0 := SplitStringIntoChars("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> r0[i] == ""[i];
}

// REPEAT 3 - TIME: 26.1580178 s

method {:test} Test3() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}

// REPEAT 4 - TIME: 33.560147 s

method {:test} Test4() {
var r0 := SplitStringIntoChars("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> r0[i] == "aa"[i];
}

// REPEAT 5 - TIME: 42.1190909 s

method {:test} Test5() {
var r0 := SplitStringIntoChars("\0a\U{0002}");
expect |r0| == |"\0a\U{0002}"|;
expect forall i :: 0 <= i < |"\0a\U{0002}"| ==> r0[i] == "\0a\U{0002}"[i];
}

// REPEAT 6 - TIME: 49.8423347 s

method {:test} Test6() {
var r0 := SplitStringIntoChars("\0aa");
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[i];
}

// REPEAT 7 - TIME: 58.2016374 s

method {:test} Test7() {
var r0 := SplitStringIntoChars("\0a\U{0002}aaaaaaaaaaaaa\U{0006}aaaaaaaaaa\U{0004}");
expect |r0| == |"\0a\U{0002}aaaaaaaaaaaaa\U{0006}aaaaaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\0a\U{0002}aaaaaaaaaaaaa\U{0006}aaaaaaaaaa\U{0004}"| ==> r0[i] == "\0a\U{0002}aaaaaaaaaaaaa\U{0006}aaaaaaaaaa\U{0004}"[i];
}

// REPEAT 8 - TIME: 68.0364649 s

method {:test} Test8() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}

// REPEAT 9 - TIME: 77.5700397 s

method {:test} Test9() {
var r0 := SplitStringIntoChars("\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a\U{0006}");
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a\U{0006}"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a\U{0006}"| ==> r0[i] == "\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}a\U{0006}"[i];
}

// REPEAT 10 - TIME: 87.9850952 s
