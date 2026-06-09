
method {:test} Test7() {
var seqint0 : seq<int> := [14, 9, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 8 - TIME: 14.2554415 s