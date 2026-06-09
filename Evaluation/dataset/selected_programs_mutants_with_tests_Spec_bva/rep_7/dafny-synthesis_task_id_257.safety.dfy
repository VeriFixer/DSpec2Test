method {:testEntry} Swap(a: int, b: int) returns (result: seq<int>)
    ensures |result| == 2
    ensures result[0] == b
    ensures result[1] == a
{
    result := [b, a];
}

method {:test} Test13() {
var r0 := Swap(37, 36);
expect |r0| == 2;
expect r0[0] == 36;
expect r0[1] == 37;
}

// REPEAT 7 - TIME: 10.6404455 s
