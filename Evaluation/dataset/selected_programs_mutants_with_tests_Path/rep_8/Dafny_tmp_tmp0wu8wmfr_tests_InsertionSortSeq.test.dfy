
method {:test} Test7() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 11];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 8 - TIME: 531.9683894 s