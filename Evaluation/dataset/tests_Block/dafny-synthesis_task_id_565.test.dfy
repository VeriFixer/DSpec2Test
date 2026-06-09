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
var r0 := SplitStringIntoChars("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[i];
}

// REPEAT 1 - TIME: 2.2034484 s

method {:test} Test1() {
var r0 := SplitStringIntoChars("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[i];
}

// REPEAT 2 - TIME: 3.0167011 s

method {:test} Test2() {
var r0 := SplitStringIntoChars("\0aa");
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[i];
}

// REPEAT 3 - TIME: 3.7439495 s

method {:test} Test3() {
var r0 := SplitStringIntoChars("\0aaa");
expect |r0| == |"\0aaa"|;
expect forall i :: 0 <= i < |"\0aaa"| ==> r0[i] == "\0aaa"[i];
}

// REPEAT 4 - TIME: 4.5476126 s

method {:test} Test4() {
var r0 := SplitStringIntoChars("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[i];
}

// REPEAT 5 - TIME: 5.253141 s

method {:test} Test5() {
var r0 := SplitStringIntoChars("\0aa\U{0002}");
expect |r0| == |"\0aa\U{0002}"|;
expect forall i :: 0 <= i < |"\0aa\U{0002}"| ==> r0[i] == "\0aa\U{0002}"[i];
}

// REPEAT 6 - TIME: 6.0565761 s

method {:test} Test6() {
var r0 := SplitStringIntoChars("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[i];
}

// REPEAT 7 - TIME: 6.749251 s

method {:test} Test7() {
var r0 := SplitStringIntoChars("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[i];
}

// REPEAT 8 - TIME: 7.4542424 s

method {:test} Test8() {
var r0 := SplitStringIntoChars("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[i];
}

// REPEAT 9 - TIME: 8.0449101 s

method {:test} Test9() {
var r0 := SplitStringIntoChars("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[i];
}

// REPEAT 10 - TIME: 8.7791557 s
