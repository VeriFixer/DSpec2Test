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

method {:test} Test13() {
var r0 := ReplaceBlanksWithChar("a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa ", '\0');
expect |r0| == |"a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "| ==> ("a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "[i] == ' ' ==> r0[i] == '\0') && ("a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "[i] != ' ' ==> r0[i] == "a  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa "[i]);
}

// REPEAT 5 - TIME: 9.3996555 s
