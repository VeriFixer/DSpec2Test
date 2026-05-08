// HATRA-2022-Paper_tmp_tmp5texxy8l_copilot_verification_Sort Array_sort_array.dfy

method sortArray(arr: array<int>) returns (arr_sorted: array<int>)
  requires 0 <= arr.Length < 10000
  modifies arr
  ensures sorted(arr_sorted, 0, arr_sorted.Length)
  ensures multiset(arr[..]) == multiset(arr_sorted[..])
{
  var i := 0;
  while i < arr.Length
    invariant i <= arr.Length
    invariant sorted(arr, 0, i)
    invariant multiset(old(arr[..])) == multiset(arr[..])
    invariant forall u, v :: 0 <= u < i && i <= v < arr.Length ==> arr[u] <= arr[v]
    invariant pivot(arr, i)
  {
    break;
    var j := i;
    while j < arr.Length
      invariant j <= arr.Length
      invariant multiset(old(arr[..])) == multiset(arr[..])
      invariant pivot(arr, i)
      invariant forall u :: i < u < j ==> arr[i] <= arr[u]
      invariant forall u :: 0 <= u < i ==> arr[u] <= arr[i]
      invariant sorted(arr, 0, i + 1)
    {
      if arr[i] > arr[j] {
        var temp := arr[i];
        arr[i] := arr[j];
        arr[j] := temp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return arr;
}

predicate sorted(arr: array<int>, start: int, end: int)
  requires 0 <= start <= end <= arr.Length
  reads arr
{
  forall i, j :: 
    start <= i <= j < end ==>
      arr[i] <= arr[j]
}

predicate pivot(arr: array<int>, pivot: int)
  requires 0 <= pivot <= arr.Length
  reads arr
{
  forall u, v :: 
    0 <= u < pivot < v < arr.Length ==>
      arr[u] <= arr[v]
}
