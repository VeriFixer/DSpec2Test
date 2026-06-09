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
method {:test} Test1() {
var r0 := SplitStringIntoChars("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> r0[i] == ""[i];
}
method {:test} Test3() {
var r0 := SplitStringIntoChars("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> r0[i] == "aa"[i];
}

// REPEAT 1 - TIME: 5.903906 s

method {:test} Test10() {
var r0 := SplitStringIntoChars("a\0a");
expect |r0| == |"a\0a"|;
expect forall i :: 0 <= i < |"a\0a"| ==> r0[i] == "a\0a"[i];
}

// REPEAT 2 - TIME: 6.7440745 s

method {:test} Test11() {
var r0 := SplitStringIntoChars("\U{0002}\0");
expect |r0| == |"\U{0002}\0"|;
expect forall i :: 0 <= i < |"\U{0002}\0"| ==> r0[i] == "\U{0002}\0"[i];
}

// REPEAT 3 - TIME: 7.3581826 s

method {:test} Test12() {
var r0 := SplitStringIntoChars("a\0aaaaaaaaaaaa\U{0002}");
expect |r0| == |"a\0aaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaa\U{0002}"| ==> r0[i] == "a\0aaaaaaaaaaaa\U{0002}"[i];
}

// REPEAT 4 - TIME: 7.9447985 s

method {:test} Test13() {
var r0 := SplitStringIntoChars("\U{0002}\0");
expect |r0| == |"\U{0002}\0"|;
expect forall i :: 0 <= i < |"\U{0002}\0"| ==> r0[i] == "\U{0002}\0"[i];
}

// REPEAT 5 - TIME: 8.4682933 s

method {:test} Test14() {
var r0 := SplitStringIntoChars("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[i];
}

// REPEAT 6 - TIME: 9.0781418 s

method {:test} Test15() {
var r0 := SplitStringIntoChars("\0a\U{0002}");
expect |r0| == |"\0a\U{0002}"|;
expect forall i :: 0 <= i < |"\0a\U{0002}"| ==> r0[i] == "\0a\U{0002}"[i];
}

// REPEAT 7 - TIME: 9.6833965 s

method {:test} Test16() {
var r0 := SplitStringIntoChars("\U{0002}\0\U{0004}a");
expect |r0| == |"\U{0002}\0\U{0004}a"|;
expect forall i :: 0 <= i < |"\U{0002}\0\U{0004}a"| ==> r0[i] == "\U{0002}\0\U{0004}a"[i];
}

// REPEAT 8 - TIME: 10.2937777 s

method {:test} Test17() {
var r0 := SplitStringIntoChars("\U{0002}\0");
expect |r0| == |"\U{0002}\0"|;
expect forall i :: 0 <= i < |"\U{0002}\0"| ==> r0[i] == "\U{0002}\0"[i];
}

// REPEAT 9 - TIME: 10.8568879 s

method {:test} Test18() {
var r0 := SplitStringIntoChars("\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect |r0| == |"\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"| ==> r0[i] == "\0aa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[i];
}

// REPEAT 10 - TIME: 11.3872887 s
