method {:testEntry} SplitAndAppend(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0 && n < |l|
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i + n) % |l|]
{
    var firstPart: seq<int> := l[..n];
    var secondPart: seq<int> := l[n..];
    r := secondPart + firstPart;
}

method {:test} Test16() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 23, 27, 0, 0, 0];
expect 8 >= 0 && 8 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 8);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 8) % |seqint0|];
}

// REPEAT 9 - TIME: 14.4655622 s
