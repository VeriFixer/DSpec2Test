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
