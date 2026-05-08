// summer-school-2020_tmp_tmpn8nf7zf0_chapter02_solutions_exercise03_solution.dfy

predicate IsSorted(s: seq<int>)
{
  forall i :: 
    0 <= i < |s| - 1 ==>
      s[i] <= s[i + 1]
}

predicate SortSpec(input: seq<int>, output: seq<int>)
{
  IsSorted(output) &&
  multiset(output) == multiset(input)
}

method merge_sort(input: seq<int>) returns (output: seq<int>)
  ensures SortSpec(input, output)
{
  if |input| == 1 {
    output := input;
  } else {
    var pivotIndex := |input| / 2;
    var left := input[..pivotIndex];
    var right := input[pivotIndex..];
    var leftSorted := left;
    leftSorted := merge_sort(left);
    var rightSorted := right;
    rightSorted := merge_sort(right);
    output := merge(leftSorted, rightSorted);
    assert left + right == input;
  }
}

method merge(a: seq<int>, b: seq<int>) returns (output: seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures SortSpec(a + b, output)
{
  var ai := 0;
  var bi := 0;
  output := [];
  while ai < |a| || bi < |b|
    invariant 0 <= ai <= |a|
    invariant 0 <= bi <= |b|
    invariant 0 < |output| && ai < |a| ==> output[|output| - 1] <= a[ai]
    invariant 0 < |output| && bi < |b| ==> output[|output| - 1] <= b[bi]
    invariant forall i :: 0 <= i < |output| - 1 ==> output[i] <= output[i + 1]
    invariant multiset(output) == multiset(a[..ai]) + multiset(b[..bi])
    decreases |a| - ai + |b| - bi
  {
    ghost var outputo := output;
    ghost var ao := ai;
    ghost var bo := bi;
    if ai == |a| || (bi < |b| && a[ai] > b[bi]) {
      output := output + [b[bi]];
      bi := bi + 1;
      assert b[bo .. bi] == [b[bo]];
    } else {
      output := output + [a[ai]];
      ai := ai + 1;
      assert a[ao .. ai] == [a[ao]];
    }
    assert a[..ai] == a[..ao] + a[ao .. ai];
    assert b[..bi] == b[..bo] + b[bo .. bi];
  }
  assert a == a[..ai];
  assert b == b[..bi];
}

method fast_sort(input: seq<int>) returns (output: seq<int>)
{
  output := [1, 2, 3];
}
