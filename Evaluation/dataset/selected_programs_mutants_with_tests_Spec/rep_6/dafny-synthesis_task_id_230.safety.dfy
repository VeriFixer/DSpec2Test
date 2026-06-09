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

method {:test} Test5() {
var r0 := ReplaceBlanksWithChar("a\U{0001}aaaaaaaaaaaa\U{0003}", '\0');
expect |r0| == |"a\U{0001}aaaaaaaaaaaa\U{0003}"|;
expect forall i :: 0 <= i < |"a\U{0001}aaaaaaaaaaaa\U{0003}"| ==> ("a\U{0001}aaaaaaaaaaaa\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("a\U{0001}aaaaaaaaaaaa\U{0003}"[i] != ' ' ==> r0[i] == "a\U{0001}aaaaaaaaaaaa\U{0003}"[i]);
}

// REPEAT 6 - TIME: 6.7280067 s
