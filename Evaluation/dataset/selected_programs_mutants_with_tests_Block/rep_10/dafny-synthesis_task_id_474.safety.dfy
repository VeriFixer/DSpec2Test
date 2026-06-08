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

// REPEAT 10 - TIME: 19.2168897 s
