method {:testEntry} Swap(a: int, b: int) returns (result: seq<int>)
    ensures |result| == 2
    ensures result[0] == b
    ensures result[1] == a
{
    result := [b, a];
}

method {:test} Test4() {
var r0 := Swap(32, 33);
expect |r0| == 2;
expect r0[0] == 33;
expect r0[1] == 32;
}

// REPEAT 5 - TIME: 8.4487655 s
