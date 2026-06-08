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

method {:test} Test15() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"| ==> ("aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"[i]);
}
method {:test} Test16() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test17() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\0');
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 6 - TIME: 10.6315417 s
