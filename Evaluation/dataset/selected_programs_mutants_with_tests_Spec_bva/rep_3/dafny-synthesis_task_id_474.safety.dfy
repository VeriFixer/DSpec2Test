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

method {:test} Test11() {
var r0 := ReplaceChars("aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}", '\U{0001}', '\0');
expect |r0| == |"aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"|;
expect forall i :: 0 <= i < |"aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"| ==> ("aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"[i] != '\U{0001}' ==> r0[i] == "aaaa\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}"[i]);
}

// REPEAT 3 - TIME: 8.122064 s
