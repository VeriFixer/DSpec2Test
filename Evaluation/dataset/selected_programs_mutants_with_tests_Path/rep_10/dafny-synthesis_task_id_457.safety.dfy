method {:testEntry} MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
    requires |s| > 0
    ensures minSublist in s
    ensures forall sublist :: sublist in s ==> |minSublist| <= |sublist|
{
    minSublist := s[0];
    for i := 1 to |s|
        invariant 0 <= i <= |s|
        invariant minSublist in s[..i]
        invariant forall sublist :: sublist in s[..i] ==> |minSublist| <= |sublist|
    {
        if |s[i]| < |minSublist| {
            minSublist := s[i];
        }
    }
}

method {:test} Test9() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint4 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint5 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint6 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint7 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint8 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint9 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint10 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint11 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint12 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint13 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint14 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint15 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint16 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint17 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint18 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint19 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint20 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint21 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint22 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint23 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint24 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint25 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint26 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint27 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint28 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint29 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint30 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint31 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint32 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint33 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint34 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint35 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint36 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint37 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint38 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint39 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint40 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint41 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint42 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint43 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint44 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint45 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint46 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint47 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint48 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint49 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45, seqint46, seqint47, seqint48, seqint49];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MinLengthSublist(seqseqint0);
expect r0 in seqseqint0;
expect forall sublist :: sublist in seqseqint0 ==> |r0| <= |sublist|;
}

// REPEAT 10 - TIME: 509.9831902 s
