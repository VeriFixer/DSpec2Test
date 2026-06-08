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

method {:test} Test3() {
var r0 := ReplaceBlanksWithChar("aa", '\0');
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> ("aa"[i] == ' ' ==> r0[i] == '\0') && ("aa"[i] != ' ' ==> r0[i] == "aa"[i]);
}
method {:test} Test4() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaaaaaaaaaaaaaaa\U{0003}", '\0');
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaa\U{0003}"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaa\U{0003}"| ==> (" aaaaaaaaaaaaaaaaaaaaa\U{0003}"[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaaaaaaaaaaaaaaa\U{0003}"[i] != ' ' ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaa\U{0003}"[i]);
}
method {:test} Test5() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaa ", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaa "| ==> ("aaaaaaaaaaaaaaaaaaaaaa "[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaa "[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaa "[i]);
}

// REPEAT 2 - TIME: 4.4096447 s
