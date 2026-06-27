method {:testEntry} AllCharactersSame(s: string) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
    ensures !result ==> (|s| > 1) && (exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j])
{
    if |s| <= 1 {
        return true;
    }

    var firstChar := s[0];
    result := true;

    for i := 1 to |s|
        invariant 0 <= i <= |s|
        invariant result ==> forall k :: 0 <= k < i ==> s[k] == firstChar
    {
        if s[i] != firstChar {
            result := false;
            break;
        }
    }
}

method {:test} Test0() {
var r0 := AllCharactersSame("\0\U{0002}");
expect r0 ==> forall i, j :: 0 <= i < |"\0\U{0002}"| && 0 <= j < |"\0\U{0002}"| ==> "\0\U{0002}"[i] == "\0\U{0002}"[j];
expect !r0 ==> |"\0\U{0002}"| > 1 && exists i, j :: 0 <= i < |"\0\U{0002}"| && 0 <= j < |"\0\U{0002}"| && i != j && "\0\U{0002}"[i] != "\0\U{0002}"[j];
}
method {:test} Test1() {
var r0 := AllCharactersSame("");
expect r0 ==> forall i, j :: 0 <= i < |""| && 0 <= j < |""| ==> ""[i] == ""[j];
expect !r0 ==> |""| > 1 && exists i, j :: 0 <= i < |""| && 0 <= j < |""| && i != j && ""[i] != ""[j];
}

// REPEAT 1 - TIME: 3.7404116 s

method {:test} Test2() {
var r0 := AllCharactersSame("\0\U{0002}a");
expect r0 ==> forall i, j :: 0 <= i < |"\0\U{0002}a"| && 0 <= j < |"\0\U{0002}a"| ==> "\0\U{0002}a"[i] == "\0\U{0002}a"[j];
expect !r0 ==> |"\0\U{0002}a"| > 1 && exists i, j :: 0 <= i < |"\0\U{0002}a"| && 0 <= j < |"\0\U{0002}a"| && i != j && "\0\U{0002}a"[i] != "\0\U{0002}a"[j];
}
method {:test} Test3() {
var r0 := AllCharactersSame("\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0"| && 0 <= j < |"\0"| ==> "\0"[i] == "\0"[j];
expect !r0 ==> |"\0"| > 1 && exists i, j :: 0 <= i < |"\0"| && 0 <= j < |"\0"| && i != j && "\0"[i] != "\0"[j];
}

// REPEAT 2 - TIME: 5.0468273 s

method {:test} Test4() {
var r0 := AllCharactersSame("aa\0\U{0002}aaaaaaaaaa\U{0004}aaaa\U{0006}");
expect r0 ==> forall i, j :: 0 <= i < |"aa\0\U{0002}aaaaaaaaaa\U{0004}aaaa\U{0006}"| && 0 <= j < |"aa\0\U{0002}aaaaaaaaaa\U{0004}aaaa\U{0006}"| ==> "aa\0\U{0002}aaaaaaaaaa\U{0004}aaaa\U{0006}"[i] == "aa\0\U{0002}aaaaaaaaaa\U{0004}aaaa\U{0006}"[j];
expect !r0 ==> |"aa\0\U{0002}aaaaaaaaaa\U{0004}aaaa\U{0006}"| > 1 && exists i, j :: 0 <= i < |"aa\0\U{0002}aaaaaaaaaa\U{0004}aaaa\U{0006}"| && 0 <= j < |"aa\0\U{0002}aaaaaaaaaa\U{0004}aaaa\U{0006}"| && i != j && "aa\0\U{0002}aaaaaaaaaa\U{0004}aaaa\U{0006}"[i] != "aa\0\U{0002}aaaaaaaaaa\U{0004}aaaa\U{0006}"[j];
}
method {:test} Test5() {
var r0 := AllCharactersSame("a\0aaaaaaaaaa\0\0\0");
expect r0 ==> forall i, j :: 0 <= i < |"a\0aaaaaaaaaa\0\0\0"| && 0 <= j < |"a\0aaaaaaaaaa\0\0\0"| ==> "a\0aaaaaaaaaa\0\0\0"[i] == "a\0aaaaaaaaaa\0\0\0"[j];
expect !r0 ==> |"a\0aaaaaaaaaa\0\0\0"| > 1 && exists i, j :: 0 <= i < |"a\0aaaaaaaaaa\0\0\0"| && 0 <= j < |"a\0aaaaaaaaaa\0\0\0"| && i != j && "a\0aaaaaaaaaa\0\0\0"[i] != "a\0aaaaaaaaaa\0\0\0"[j];
}

// REPEAT 3 - TIME: 6.1880311 s

method {:test} Test6() {
var r0 := AllCharactersSame("\U{0002}\0");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0002}\0"| && 0 <= j < |"\U{0002}\0"| ==> "\U{0002}\0"[i] == "\U{0002}\0"[j];
expect !r0 ==> |"\U{0002}\0"| > 1 && exists i, j :: 0 <= i < |"\U{0002}\0"| && 0 <= j < |"\U{0002}\0"| && i != j && "\U{0002}\0"[i] != "\U{0002}\0"[j];
}
method {:test} Test7() {
var r0 := AllCharactersSame("a\0aaaaa\0\0");
expect r0 ==> forall i, j :: 0 <= i < |"a\0aaaaa\0\0"| && 0 <= j < |"a\0aaaaa\0\0"| ==> "a\0aaaaa\0\0"[i] == "a\0aaaaa\0\0"[j];
expect !r0 ==> |"a\0aaaaa\0\0"| > 1 && exists i, j :: 0 <= i < |"a\0aaaaa\0\0"| && 0 <= j < |"a\0aaaaa\0\0"| && i != j && "a\0aaaaa\0\0"[i] != "a\0aaaaa\0\0"[j];
}

// REPEAT 4 - TIME: 7.5221772 s

method {:test} Test8() {
var r0 := AllCharactersSame("\U{0006}\0\U{0002}\U{0004}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0006}\0\U{0002}\U{0004}"| && 0 <= j < |"\U{0006}\0\U{0002}\U{0004}"| ==> "\U{0006}\0\U{0002}\U{0004}"[i] == "\U{0006}\0\U{0002}\U{0004}"[j];
expect !r0 ==> |"\U{0006}\0\U{0002}\U{0004}"| > 1 && exists i, j :: 0 <= i < |"\U{0006}\0\U{0002}\U{0004}"| && 0 <= j < |"\U{0006}\0\U{0002}\U{0004}"| && i != j && "\U{0006}\0\U{0002}\U{0004}"[i] != "\U{0006}\0\U{0002}\U{0004}"[j];
}
method {:test} Test9() {
var r0 := AllCharactersSame("\0\0aaaaa\0a\0aaaaa\0aaaa\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0aaaaa\0a\0aaaaa\0aaaa\0"| && 0 <= j < |"\0\0aaaaa\0a\0aaaaa\0aaaa\0"| ==> "\0\0aaaaa\0a\0aaaaa\0aaaa\0"[i] == "\0\0aaaaa\0a\0aaaaa\0aaaa\0"[j];
expect !r0 ==> |"\0\0aaaaa\0a\0aaaaa\0aaaa\0"| > 1 && exists i, j :: 0 <= i < |"\0\0aaaaa\0a\0aaaaa\0aaaa\0"| && 0 <= j < |"\0\0aaaaa\0a\0aaaaa\0aaaa\0"| && i != j && "\0\0aaaaa\0a\0aaaaa\0aaaa\0"[i] != "\0\0aaaaa\0a\0aaaaa\0aaaa\0"[j];
}

// REPEAT 5 - TIME: 8.8942597 s

method {:test} Test10() {
var r0 := AllCharactersSame("\U{0004}\0\U{0002}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0004}\0\U{0002}"| && 0 <= j < |"\U{0004}\0\U{0002}"| ==> "\U{0004}\0\U{0002}"[i] == "\U{0004}\0\U{0002}"[j];
expect !r0 ==> |"\U{0004}\0\U{0002}"| > 1 && exists i, j :: 0 <= i < |"\U{0004}\0\U{0002}"| && 0 <= j < |"\U{0004}\0\U{0002}"| && i != j && "\U{0004}\0\U{0002}"[i] != "\U{0004}\0\U{0002}"[j];
}
method {:test} Test11() {
var r0 := AllCharactersSame("\0aa");
expect r0 ==> forall i, j :: 0 <= i < |"\0aa"| && 0 <= j < |"\0aa"| ==> "\0aa"[i] == "\0aa"[j];
expect !r0 ==> |"\0aa"| > 1 && exists i, j :: 0 <= i < |"\0aa"| && 0 <= j < |"\0aa"| && i != j && "\0aa"[i] != "\0aa"[j];
}

// REPEAT 6 - TIME: 10.2836375 s

method {:test} Test12() {
var r0 := AllCharactersSame("\U{000E}\U{0010}aaa\0a\U{0002}a\U{0008}aaaaa\n\U{0006}aa\U{0004}\U{000C}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{000E}\U{0010}aaa\0a\U{0002}a\U{0008}aaaaa\n\U{0006}aa\U{0004}\U{000C}"| && 0 <= j < |"\U{000E}\U{0010}aaa\0a\U{0002}a\U{0008}aaaaa\n\U{0006}aa\U{0004}\U{000C}"| ==> "\U{000E}\U{0010}aaa\0a\U{0002}a\U{0008}aaaaa\n\U{0006}aa\U{0004}\U{000C}"[i] == "\U{000E}\U{0010}aaa\0a\U{0002}a\U{0008}aaaaa\n\U{0006}aa\U{0004}\U{000C}"[j];
expect !r0 ==> |"\U{000E}\U{0010}aaa\0a\U{0002}a\U{0008}aaaaa\n\U{0006}aa\U{0004}\U{000C}"| > 1 && exists i, j :: 0 <= i < |"\U{000E}\U{0010}aaa\0a\U{0002}a\U{0008}aaaaa\n\U{0006}aa\U{0004}\U{000C}"| && 0 <= j < |"\U{000E}\U{0010}aaa\0a\U{0002}a\U{0008}aaaaa\n\U{0006}aa\U{0004}\U{000C}"| && i != j && "\U{000E}\U{0010}aaa\0a\U{0002}a\U{0008}aaaaa\n\U{0006}aa\U{0004}\U{000C}"[i] != "\U{000E}\U{0010}aaa\0a\U{0002}a\U{0008}aaaaa\n\U{0006}aa\U{0004}\U{000C}"[j];
}
method {:test} Test13() {
var r0 := AllCharactersSame("\0aa\0\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0aa\0\0"| && 0 <= j < |"\0aa\0\0"| ==> "\0aa\0\0"[i] == "\0aa\0\0"[j];
expect !r0 ==> |"\0aa\0\0"| > 1 && exists i, j :: 0 <= i < |"\0aa\0\0"| && 0 <= j < |"\0aa\0\0"| && i != j && "\0aa\0\0"[i] != "\0aa\0\0"[j];
}

// REPEAT 7 - TIME: 11.7118769 s

method {:test} Test14() {
var r0 := AllCharactersSame("\U{0004}\U{0008}a\0\U{0002}\U{0006}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0004}\U{0008}a\0\U{0002}\U{0006}"| && 0 <= j < |"\U{0004}\U{0008}a\0\U{0002}\U{0006}"| ==> "\U{0004}\U{0008}a\0\U{0002}\U{0006}"[i] == "\U{0004}\U{0008}a\0\U{0002}\U{0006}"[j];
expect !r0 ==> |"\U{0004}\U{0008}a\0\U{0002}\U{0006}"| > 1 && exists i, j :: 0 <= i < |"\U{0004}\U{0008}a\0\U{0002}\U{0006}"| && 0 <= j < |"\U{0004}\U{0008}a\0\U{0002}\U{0006}"| && i != j && "\U{0004}\U{0008}a\0\U{0002}\U{0006}"[i] != "\U{0004}\U{0008}a\0\U{0002}\U{0006}"[j];
}
method {:test} Test15() {
var r0 := AllCharactersSame("\0\0\0\0\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0\0\0\0"| && 0 <= j < |"\0\0\0\0\0"| ==> "\0\0\0\0\0"[i] == "\0\0\0\0\0"[j];
expect !r0 ==> |"\0\0\0\0\0"| > 1 && exists i, j :: 0 <= i < |"\0\0\0\0\0"| && 0 <= j < |"\0\0\0\0\0"| && i != j && "\0\0\0\0\0"[i] != "\0\0\0\0\0"[j];
}

// REPEAT 8 - TIME: 12.8860988 s

method {:test} Test16() {
var r0 := AllCharactersSame("\U{0004}a\U{0006}\0\U{0002}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0004}a\U{0006}\0\U{0002}"| && 0 <= j < |"\U{0004}a\U{0006}\0\U{0002}"| ==> "\U{0004}a\U{0006}\0\U{0002}"[i] == "\U{0004}a\U{0006}\0\U{0002}"[j];
expect !r0 ==> |"\U{0004}a\U{0006}\0\U{0002}"| > 1 && exists i, j :: 0 <= i < |"\U{0004}a\U{0006}\0\U{0002}"| && 0 <= j < |"\U{0004}a\U{0006}\0\U{0002}"| && i != j && "\U{0004}a\U{0006}\0\U{0002}"[i] != "\U{0004}a\U{0006}\0\U{0002}"[j];
}
method {:test} Test17() {
var r0 := AllCharactersSame("\0\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0"| && 0 <= j < |"\0\0"| ==> "\0\0"[i] == "\0\0"[j];
expect !r0 ==> |"\0\0"| > 1 && exists i, j :: 0 <= i < |"\0\0"| && 0 <= j < |"\0\0"| && i != j && "\0\0"[i] != "\0\0"[j];
}

// REPEAT 9 - TIME: 14.0763101 s

method {:test} Test18() {
var r0 := AllCharactersSame("\U{0004}aaa\0\U{0008}a\U{0002}\n\U{0006}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0004}aaa\0\U{0008}a\U{0002}\n\U{0006}"| && 0 <= j < |"\U{0004}aaa\0\U{0008}a\U{0002}\n\U{0006}"| ==> "\U{0004}aaa\0\U{0008}a\U{0002}\n\U{0006}"[i] == "\U{0004}aaa\0\U{0008}a\U{0002}\n\U{0006}"[j];
expect !r0 ==> |"\U{0004}aaa\0\U{0008}a\U{0002}\n\U{0006}"| > 1 && exists i, j :: 0 <= i < |"\U{0004}aaa\0\U{0008}a\U{0002}\n\U{0006}"| && 0 <= j < |"\U{0004}aaa\0\U{0008}a\U{0002}\n\U{0006}"| && i != j && "\U{0004}aaa\0\U{0008}a\U{0002}\n\U{0006}"[i] != "\U{0004}aaa\0\U{0008}a\U{0002}\n\U{0006}"[j];
}
method {:test} Test19() {
var r0 := AllCharactersSame("\0\0\0aa\0\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0\0aa\0\0"| && 0 <= j < |"\0\0\0aa\0\0"| ==> "\0\0\0aa\0\0"[i] == "\0\0\0aa\0\0"[j];
expect !r0 ==> |"\0\0\0aa\0\0"| > 1 && exists i, j :: 0 <= i < |"\0\0\0aa\0\0"| && 0 <= j < |"\0\0\0aa\0\0"| && i != j && "\0\0\0aa\0\0"[i] != "\0\0\0aa\0\0"[j];
}

// REPEAT 10 - TIME: 15.1053757 s
