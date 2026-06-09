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

// REPEAT 1 - TIME: 11.7360235 s

method {:test} Test1() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}

// REPEAT 2 - TIME: 19.8897154 s

method {:test} Test2() {
var r0 := SplitStringIntoChars("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> r0[i] == ""[i];
}

// REPEAT 3 - TIME: 30.1794813 s

method {:test} Test3() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}

// REPEAT 4 - TIME: 43.0603688 s

method {:test} Test4() {
var r0 := SplitStringIntoChars("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> r0[i] == "aa"[i];
}

// REPEAT 5 - TIME: 53.2925278 s

method {:test} Test5() {
var r0 := SplitStringIntoChars("\0a\U{0002}");
expect |r0| == |"\0a\U{0002}"|;
expect forall i :: 0 <= i < |"\0a\U{0002}"| ==> r0[i] == "\0a\U{0002}"[i];
}

// REPEAT 6 - TIME: 65.2466615 s

method {:test} Test6() {
var r0 := SplitStringIntoChars("\0aa");
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[i];
}

// REPEAT 7 - TIME: 76.8181708 s

method {:test} Test7() {
var r0 := SplitStringIntoChars("\0a\U{0002}aaaaaaaaaa\U{0006}\U{0004}");
expect |r0| == |"\0a\U{0002}aaaaaaaaaa\U{0006}\U{0004}"|;
expect forall i :: 0 <= i < |"\0a\U{0002}aaaaaaaaaa\U{0006}\U{0004}"| ==> r0[i] == "\0a\U{0002}aaaaaaaaaa\U{0006}\U{0004}"[i];
}

// REPEAT 8 - TIME: 89.3414379 s

method {:test} Test8() {
var r0 := SplitStringIntoChars("\0aaaaaaaaaaaaa\U{0002}");
expect |r0| == |"\0aaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaa\U{0002}"| ==> r0[i] == "\0aaaaaaaaaaaaa\U{0002}"[i];
}

// REPEAT 9 - TIME: 103.350664 s

method {:test} Test9() {
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}

// REPEAT 10 - TIME: 114.401063 s
