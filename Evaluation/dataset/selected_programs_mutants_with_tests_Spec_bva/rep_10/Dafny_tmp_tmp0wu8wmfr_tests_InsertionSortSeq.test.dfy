
method {:test} Test18() {
var seqint0 : seq<int> := [28, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 34];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 10 - TIME: 26.5195714 s