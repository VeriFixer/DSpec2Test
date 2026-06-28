method {:testEntry} ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == oldChar ==> s'[k] == newChar) && (s[k] != oldChar ==> s'[k] == s[k])
    {
        if s[i] == oldChar
        {
            s' := s' + [newChar];
        }
        else 
        {
            s' := s' + [s[i]];
        }
    }
    return s';
}

method {:test} Test0() {
var r0 := ReplaceChars("a", '\U{0001}', '\0');
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> ("a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("a"[i] != '\U{0001}' ==> r0[i] == "a"[i]);
}
method {:test} Test1() {
var r0 := ReplaceChars("", '\U{0001}', '\0');
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (""[i] == '\U{0001}' ==> r0[i] == '\0') && (""[i] != '\U{0001}' ==> r0[i] == ""[i]);
}
method {:test} Test3() {
var r0 := ReplaceChars("aa", '\U{0001}', '\0');
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> ("aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aa"[i] != '\U{0001}' ==> r0[i] == "aa"[i]);
}

// REPEAT 1 - TIME: 9.372056 s

method {:test} Test10() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaa\0a", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaa\0a"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaa\0a"| ==> ("aaaaaaaaaaaaaaaaaa\0a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaa\0a"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaa\0a"[i]);
}

// REPEAT 2 - TIME: 10.5045239 s

method {:test} Test11() {
var r0 := ReplaceChars("\U{0001}a\U{0001}aaaaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}a\U{0001}aaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}a\U{0001}aaaaaaaaaaaaaaaaa\U{0001}"| ==> ("\U{0001}a\U{0001}aaaaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}a\U{0001}aaaaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}a\U{0001}aaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 3 - TIME: 11.4288063 s

method {:test} Test12() {
var r0 := ReplaceChars("\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaa\U{0001}"| ==> ("\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaa\U{0001}aaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 4 - TIME: 12.3660865 s

method {:test} Test13() {
var r0 := ReplaceChars("aaaaaa\U{0001}aaaaaaa\U{0001}aaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"aaaaaa\U{0001}aaaaaaa\U{0001}aaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaa\U{0001}aaaaaaa\U{0001}aaaaaaaa"| ==> ("aaaaaa\U{0001}aaaaaaa\U{0001}aaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaa\U{0001}aaaaaaa\U{0001}aaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "aaaaaa\U{0001}aaaaaaa\U{0001}aaaaaaaa"[i]);
}

// REPEAT 5 - TIME: 13.2920852 s

method {:test} Test14() {
var r0 := ReplaceChars("aaaaaaaa\U{0001}aaaaaaaaaaa\U{0001}\U{0001}a\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaa\U{0001}aaaaaaaaaaa\U{0001}\U{0001}a\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaaaa\U{0001}aaaaaaaaaaa\U{0001}\U{0001}a\U{0001}"| ==> ("aaaaaaaa\U{0001}aaaaaaaaaaa\U{0001}\U{0001}a\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaa\U{0001}aaaaaaaaaaa\U{0001}\U{0001}a\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaa\U{0001}aaaaaaaaaaa\U{0001}\U{0001}a\U{0001}"[i]);
}

// REPEAT 6 - TIME: 14.1558135 s

method {:test} Test15() {
var r0 := ReplaceChars("\U{0001}a\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}a\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}a\U{0001}"| ==> ("\U{0001}a\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}a\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}a\U{0001}"[i]);
}

// REPEAT 7 - TIME: 15.3030012 s

method {:test} Test16() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}a\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}a\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}a\U{0001}\U{0001}"| ==> ("\U{0001}aaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}a\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}a\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaa\U{0001}aaaaaaaaa\U{0001}\U{0001}a\U{0001}\U{0001}"[i]);
}

// REPEAT 8 - TIME: 16.3764306 s

method {:test} Test17() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}"| ==> ("\U{0001}aaaaaaaaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}"[i]);
}

// REPEAT 9 - TIME: 17.5879275 s

method {:test} Test18() {
var r0 := ReplaceChars("\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a"|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a"| ==> ("\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a"[i]);
}

// REPEAT 10 - TIME: 18.7232164 s
