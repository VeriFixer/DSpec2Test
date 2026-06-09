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
var r0 := ReplaceChars("\U{0002}", '\U{0001}', '\0');
expect |r0| == |"\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0002}"| ==> ("\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}"[i] != '\U{0001}' ==> r0[i] == "\U{0002}"[i]);
}
method {:test} Test2() {
var r0 := ReplaceChars("a\U{0001}", '\U{0001}', '\0');
expect |r0| == |"a\U{0001}"|;
expect forall i :: 0 <= i < |"a\U{0001}"| ==> ("a\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("a\U{0001}"[i] != '\U{0001}' ==> r0[i] == "a\U{0001}"[i]);
}

// REPEAT 1 - TIME: 3.2014154 s

method {:test} Test3() {
var r0 := ReplaceChars("\U{0002}a", '\U{0001}', '\0');
expect |r0| == |"\U{0002}a"|;
expect forall i :: 0 <= i < |"\U{0002}a"| ==> ("\U{0002}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}a"[i] != '\U{0001}' ==> r0[i] == "\U{0002}a"[i]);
}
method {:test} Test4() {
var r0 := ReplaceChars("\U{0006}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", '\U{0001}', '\0');
expect |r0| == |"\U{0006}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0006}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| ==> ("\U{0006}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0006}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] != '\U{0001}' ==> r0[i] == "\U{0006}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i]);
}
method {:test} Test5() {
var r0 := ReplaceChars("\U{0003}\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0003}\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0003}\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> ("\U{0003}\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0003}\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0003}\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 2 - TIME: 4.7524441 s

method {:test} Test6() {
var r0 := ReplaceChars("", '\U{0001}', '\0');
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (""[i] == '\U{0001}' ==> r0[i] == '\0') && (""[i] != '\U{0001}' ==> r0[i] == ""[i]);
}
method {:test} Test7() {
var r0 := ReplaceChars("\U{0002}aa", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aa"|;
expect forall i :: 0 <= i < |"\U{0002}aa"| ==> ("\U{0002}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aa"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aa"[i]);
}
method {:test} Test8() {
var r0 := ReplaceChars("\U{0001}aa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aa"|;
expect forall i :: 0 <= i < |"\U{0001}aa"| ==> ("\U{0001}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aa"[i]);
}

// REPEAT 3 - TIME: 6.3899547 s

method {:test} Test9() {
var r0 := ReplaceChars("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"| ==> ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"[i]);
}
method {:test} Test10() {
var r0 := ReplaceChars("\U{0004}a\U{0002}\U{0006}", '\U{0001}', '\0');
expect |r0| == |"\U{0004}a\U{0002}\U{0006}"|;
expect forall i :: 0 <= i < |"\U{0004}a\U{0002}\U{0006}"| ==> ("\U{0004}a\U{0002}\U{0006}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0004}a\U{0002}\U{0006}"[i] != '\U{0001}' ==> r0[i] == "\U{0004}a\U{0002}\U{0006}"[i]);
}
method {:test} Test11() {
var r0 := ReplaceChars("\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}", '\U{0001}', '\0');
expect |r0| == |"\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"| ==> ("\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"[i] != '\U{0001}' ==> r0[i] == "\U{0008}aaaaa\U{0004}a\U{0006}aa\U{0001}\U{0002}"[i]);
}

// REPEAT 4 - TIME: 8.0038669 s

method {:test} Test12() {
var r0 := ReplaceChars("\U{0006}aa\U{0002}\U{0004}", '\U{0001}', '\0');
expect |r0| == |"\U{0006}aa\U{0002}\U{0004}"|;
expect forall i :: 0 <= i < |"\U{0006}aa\U{0002}\U{0004}"| ==> ("\U{0006}aa\U{0002}\U{0004}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0006}aa\U{0002}\U{0004}"[i] != '\U{0001}' ==> r0[i] == "\U{0006}aa\U{0002}\U{0004}"[i]);
}
method {:test} Test13() {
var r0 := ReplaceChars("\U{0004}\U{0006}\U{0002}", '\U{0001}', '\0');
expect |r0| == |"\U{0004}\U{0006}\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0004}\U{0006}\U{0002}"| ==> ("\U{0004}\U{0006}\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0004}\U{0006}\U{0002}"[i] != '\U{0001}' ==> r0[i] == "\U{0004}\U{0006}\U{0002}"[i]);
}
method {:test} Test14() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaaa\U{0006}aaaa\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaa\U{0008}aa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaa\U{0006}aaaa\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaa\U{0008}aa"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaa\U{0006}aaaa\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaa\U{0008}aa"| ==> ("\U{0001}aaaaaaaaaaaa\U{0006}aaaa\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaa\U{0008}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaa\U{0006}aaaa\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaa\U{0008}aa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaaa\U{0006}aaaa\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaa\U{0008}aa"[i]);
}

// REPEAT 5 - TIME: 9.5343039 s

method {:test} Test15() {
var r0 := ReplaceChars("aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> ("aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "aaa\U{0001}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test16() {
var r0 := ReplaceChars("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test17() {
var r0 := ReplaceChars("aaaa\U{0001}a", '\U{0001}', '\0');
expect |r0| == |"aaaa\U{0001}a"|;
expect forall i :: 0 <= i < |"aaaa\U{0001}a"| ==> ("aaaa\U{0001}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaa\U{0001}a"[i] != '\U{0001}' ==> r0[i] == "aaaa\U{0001}a"[i]);
}

// REPEAT 6 - TIME: 10.9492203 s

method {:test} Test18() {
var r0 := ReplaceChars("aaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}aaa", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}aaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}aaa"| ==> ("aaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}aaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}aaa"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaa\U{0001}aaa"[i]);
}
method {:test} Test19() {
var r0 := ReplaceChars("aa\U{0002}aaaa", '\U{0001}', '\0');
expect |r0| == |"aa\U{0002}aaaa"|;
expect forall i :: 0 <= i < |"aa\U{0002}aaaa"| ==> ("aa\U{0002}aaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aa\U{0002}aaaa"[i] != '\U{0001}' ==> r0[i] == "aa\U{0002}aaaa"[i]);
}
method {:test} Test20() {
var r0 := ReplaceChars("a\U{0001}aa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}aaa\U{0006}", '\U{0001}', '\0');
expect |r0| == |"a\U{0001}aa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}aaa\U{0006}"|;
expect forall i :: 0 <= i < |"a\U{0001}aa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}aaa\U{0006}"| ==> ("a\U{0001}aa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}aaa\U{0006}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("a\U{0001}aa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}aaa\U{0006}"[i] != '\U{0001}' ==> r0[i] == "a\U{0001}aa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}aaa\U{0006}"[i]);
}

// REPEAT 7 - TIME: 12.5635605 s

method {:test} Test21() {
var r0 := ReplaceChars("aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}", '\U{0001}', '\0');
expect |r0| == |"aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}"|;
expect forall i :: 0 <= i < |"aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}"| ==> ("aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}"[i] != '\U{0001}' ==> r0[i] == "aaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}"[i]);
}
method {:test} Test22() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test23() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 8 - TIME: 13.9529472 s

method {:test} Test24() {
var r0 := ReplaceChars("aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"| ==> ("aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0001}"[i]);
}
method {:test} Test25() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"[i]);
}
method {:test} Test26() {
var r0 := ReplaceChars("\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"|;
expect forall i :: 0 <= i < |"\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"| ==> ("\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}\U{0008}\n"[i]);
}

// REPEAT 9 - TIME: 15.4766826 s

method {:test} Test27() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test28() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa"[i]);
}
method {:test} Test29() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> ("\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 10 - TIME: 17.2544374 s
