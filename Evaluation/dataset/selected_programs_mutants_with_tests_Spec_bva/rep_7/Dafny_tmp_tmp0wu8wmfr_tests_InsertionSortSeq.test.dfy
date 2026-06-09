
method {:test} Test15() {
var seqint0 : seq<int> := [23, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 17, 0, 0, 0, 0, 12, 21];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 7 - TIME: 19.1425161 s