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

method {:test} Test6() {
var r0 := ReplaceBlanksWithChar("", '\0');
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (""[i] == ' ' ==> r0[i] == '\0') && (""[i] != ' ' ==> r0[i] == ""[i]);
}
method {:test} Test7() {
var r0 := ReplaceBlanksWithChar("a\U{0001}a", '\0');
expect |r0| == |"a\U{0001}a"|;
expect forall i :: 0 <= i < |"a\U{0001}a"| ==> ("a\U{0001}a"[i] == ' ' ==> r0[i] == '\0') && ("a\U{0001}a"[i] != ' ' ==> r0[i] == "a\U{0001}a"[i]);
}
method {:test} Test8() {
var r0 := ReplaceBlanksWithChar(" aa", '\0');
expect |r0| == |" aa"|;
expect forall i :: 0 <= i < |" aa"| ==> (" aa"[i] == ' ' ==> r0[i] == '\0') && (" aa"[i] != ' ' ==> r0[i] == " aa"[i]);
}

// REPEAT 3 - TIME: 5.8769388 s
