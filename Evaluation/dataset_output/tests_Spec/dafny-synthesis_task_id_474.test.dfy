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

// REPEAT 1 - TIME: 3.0725692 s

method {:test} Test1() {
var r0 := ReplaceChars("aa", '\U{0001}', '\0');
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> ("aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aa"[i] != '\U{0001}' ==> r0[i] == "aa"[i]);
}

// REPEAT 2 - TIME: 4.1330072 s

method {:test} Test2() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaa\U{0001}a", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaa\U{0001}a"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaa\U{0001}a"| ==> ("aaaaaaaaaaaaaaaaaa\U{0001}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaa\U{0001}a"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaa\U{0001}a"[i]);
}

// REPEAT 3 - TIME: 5.4274702 s

method {:test} Test3() {
var r0 := ReplaceChars("\U{0001}a\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}a\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}a\U{0001}"| ==> ("\U{0001}a\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}a\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}a\U{0001}"[i]);
}

// REPEAT 4 - TIME: 6.654093 s

method {:test} Test4() {
var r0 := ReplaceChars("\0a\0", '\U{0001}', '\0');
expect |r0| == |"\0a\0"|;
expect forall i :: 0 <= i < |"\0a\0"| ==> ("\0a\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0a\0"[i] != '\U{0001}' ==> r0[i] == "\0a\0"[i]);
}

// REPEAT 5 - TIME: 7.7300944 s

method {:test} Test5() {
var r0 := ReplaceChars("\U{0001}a\U{0001}aaaaaaaaaaaaaaa\U{0001}a\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}a\U{0001}aaaaaaaaaaaaaaa\U{0001}a\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}a\U{0001}aaaaaaaaaaaaaaa\U{0001}a\U{0001}"| ==> ("\U{0001}a\U{0001}aaaaaaaaaaaaaaa\U{0001}a\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}a\U{0001}aaaaaaaaaaaaaaa\U{0001}a\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}a\U{0001}aaaaaaaaaaaaaaa\U{0001}a\U{0001}"[i]);
}

// REPEAT 6 - TIME: 8.5070921 s

method {:test} Test6() {
var r0 := ReplaceChars("\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0001}"| ==> ("\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}\U{0001}"[i]);
}

// REPEAT 7 - TIME: 9.2458945 s

method {:test} Test7() {
var r0 := ReplaceChars("\U{0001}aa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aa"|;
expect forall i :: 0 <= i < |"\U{0001}aa"| ==> ("\U{0001}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aa"[i]);
}

// REPEAT 8 - TIME: 9.8958878 s

method {:test} Test8() {
var r0 := ReplaceChars("\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}a", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}a"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}a"| ==> ("\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}a"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaa\U{0001}aaaaaaaaaa\U{0001}a"[i]);
}

// REPEAT 9 - TIME: 10.4920568 s

method {:test} Test9() {
var r0 := ReplaceChars("\U{0001}\U{0001}aa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}\U{0001}aa"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0001}aa"| ==> ("\U{0001}\U{0001}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}\U{0001}aa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}\U{0001}aa"[i]);
}

// REPEAT 10 - TIME: 11.0532971 s
