
method {:test} Test8() {
var seqint0 : seq<int> := [21, 12, 17, 19];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 9 - TIME: 17.0461761 s