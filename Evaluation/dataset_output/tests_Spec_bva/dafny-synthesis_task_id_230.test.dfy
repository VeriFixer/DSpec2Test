method {:testEntry} ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == ' ' ==> s'[k] == ch) && (s[k] != ' ' ==> s'[k] == s[k])
    {
        if s[i] == ' '
        {
            s' := s' + [ch];
        }
        else 
        {
            s' := s' + [s[i]];
        }
    }
    return s';
}

method {:test} Test0() {
var r0 := ReplaceBlanksWithChar("a", '\0');
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> ("a"[i] == ' ' ==> r0[i] == '\0') && ("a"[i] != ' ' ==> r0[i] == "a"[i]);
}
method {:test} Test1() {
var r0 := ReplaceBlanksWithChar("", '\0');
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (""[i] == ' ' ==> r0[i] == '\0') && (""[i] != ' ' ==> r0[i] == ""[i]);
}
method {:test} Test3() {
var r0 := ReplaceBlanksWithChar("aa", '\0');
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> ("aa"[i] == ' ' ==> r0[i] == '\0') && ("aa"[i] != ' ' ==> r0[i] == "aa"[i]);
}

// REPEAT 1 - TIME: 6.8628794 s

method {:test} Test10() {
var r0 := ReplaceBlanksWithChar(" \0", '\0');
expect |r0| == |" \0"|;
expect forall i :: 0 <= i < |" \0"| ==> (" \0"[i] == ' ' ==> r0[i] == '\0') && (" \0"[i] != ' ' ==> r0[i] == " \0"[i]);
}

// REPEAT 2 - TIME: 7.8335976 s

method {:test} Test11() {
var r0 := ReplaceBlanksWithChar("  aaaaaaaaaaaaaaaaa\U{0003}", '\0');
expect |r0| == |"  aaaaaaaaaaaaaaaaa\U{0003}"|;
expect forall i :: 0 <= i < |"  aaaaaaaaaaaaaaaaa\U{0003}"| ==> ("  aaaaaaaaaaaaaaaaa\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("  aaaaaaaaaaaaaaaaa\U{0003}"[i] != ' ' ==> r0[i] == "  aaaaaaaaaaaaaaaaa\U{0003}"[i]);
}

// REPEAT 3 - TIME: 8.5671787 s

method {:test} Test12() {
var r0 := ReplaceBlanksWithChar("aaa", '\0');
expect |r0| == |"aaa"|;
expect forall i :: 0 <= i < |"aaa"| ==> ("aaa"[i] == ' ' ==> r0[i] == '\0') && ("aaa"[i] != ' ' ==> r0[i] == "aaa"[i]);
}

// REPEAT 4 - TIME: 9.4056551 s

method {:test} Test13() {
var r0 := ReplaceBlanksWithChar("\U{0003}a\U{0001}aaaaaaaaaaaaaaaaa\U{0005}", '\0');
expect |r0| == |"\U{0003}a\U{0001}aaaaaaaaaaaaaaaaa\U{0005}"|;
expect forall i :: 0 <= i < |"\U{0003}a\U{0001}aaaaaaaaaaaaaaaaa\U{0005}"| ==> ("\U{0003}a\U{0001}aaaaaaaaaaaaaaaaa\U{0005}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0003}a\U{0001}aaaaaaaaaaaaaaaaa\U{0005}"[i] != ' ' ==> r0[i] == "\U{0003}a\U{0001}aaaaaaaaaaaaaaaaa\U{0005}"[i]);
}

// REPEAT 5 - TIME: 10.1896387 s

method {:test} Test14() {
var r0 := ReplaceBlanksWithChar(" a  ", '\0');
expect |r0| == |" a  "|;
expect forall i :: 0 <= i < |" a  "| ==> (" a  "[i] == ' ' ==> r0[i] == '\0') && (" a  "[i] != ' ' ==> r0[i] == " a  "[i]);
}

// REPEAT 6 - TIME: 11.009894 s

method {:test} Test15() {
var r0 := ReplaceBlanksWithChar("\0a\0a\0aaaaaaaaaaaaa\0a\0", '\0');
expect |r0| == |"\0a\0a\0aaaaaaaaaaaaa\0a\0"|;
expect forall i :: 0 <= i < |"\0a\0a\0aaaaaaaaaaaaa\0a\0"| ==> ("\0a\0a\0aaaaaaaaaaaaa\0a\0"[i] == ' ' ==> r0[i] == '\0') && ("\0a\0a\0aaaaaaaaaaaaa\0a\0"[i] != ' ' ==> r0[i] == "\0a\0a\0aaaaaaaaaaaaa\0a\0"[i]);
}

// REPEAT 7 - TIME: 11.6764666 s

method {:test} Test16() {
var r0 := ReplaceBlanksWithChar("\U{0003}aaa\U{0001}aaaaaaaaaaaaaaaaa", '\0');
expect |r0| == |"\U{0003}aaa\U{0001}aaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0003}aaa\U{0001}aaaaaaaaaaaaaaaaa"| ==> ("\U{0003}aaa\U{0001}aaaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("\U{0003}aaa\U{0001}aaaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == "\U{0003}aaa\U{0001}aaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 8 - TIME: 12.5005282 s

method {:test} Test17() {
var r0 := ReplaceBlanksWithChar(" aaa a aaaaaaaaaaaaa aa", '\0');
expect |r0| == |" aaa a aaaaaaaaaaaaa aa"|;
expect forall i :: 0 <= i < |" aaa a aaaaaaaaaaaaa aa"| ==> (" aaa a aaaaaaaaaaaaa aa"[i] == ' ' ==> r0[i] == '\0') && (" aaa a aaaaaaaaaaaaa aa"[i] != ' ' ==> r0[i] == " aaa a aaaaaaaaaaaaa aa"[i]);
}

// REPEAT 9 - TIME: 13.2792539 s

method {:test} Test18() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaaaaaaaaaaaaa  aa", '\0');
expect |r0| == |" aaaaaaaaaaaaaaaaaaa  aa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaa  aa"| ==> (" aaaaaaaaaaaaaaaaaaa  aa"[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaaaaaaaaaaaaa  aa"[i] != ' ' ==> r0[i] == " aaaaaaaaaaaaaaaaaaa  aa"[i]);
}

// REPEAT 10 - TIME: 14.0703533 s
