
method {:test} Test17() {
var seqint0 : seq<int> := [27, 0, 0, 18, 25];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 9 - TIME: 25.2117581 s