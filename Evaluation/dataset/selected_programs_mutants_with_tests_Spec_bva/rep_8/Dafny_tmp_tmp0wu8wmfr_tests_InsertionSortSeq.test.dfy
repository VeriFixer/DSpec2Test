
method {:test} Test16() {
var seqint0 : seq<int> := [24, 0, 15, 20];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 8 - TIME: 23.7382477 s