method {:testEntry} twoSum(nums: seq<int>, target: int) returns (i: int, j: int)
  requires |nums| > 1
  requires exists i,j::0 <= i < j < |nums| &&  nums[i] + nums[j] == target
  ensures 0 <= i < j < |nums| && nums[i] + nums[j] == target
  ensures forall ii,jj:: (0 <= ii < i && ii < jj < |nums|)  ==> nums[ii] + nums[jj] != target
  ensures forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
{
  var n := |nums|;
  i := 0;
  j := 1;
  while i < n - 1
    invariant 0 <= i < j <= n
    invariant forall ii, jj :: 0 <= ii < i && ii < jj < n ==> nums[ii] + nums[jj] != target
  {
    j := i + 1;
    while j < n
      invariant 0 <= i < j <= n
      invariant forall jj :: i < jj < j ==> nums[i] + nums[jj] != target
    {
      if nums[i] + nums[j] == target {
        return;
      }
      j := j + 1;
    }

    i := i + 1;
  }
}

method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 2998, 3000, 2998, 2999, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2997, 2996];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i, j :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 5996, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 5996);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 5996;
expect forall ii, jj :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 5996;
expect forall jj :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 5996;
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1142, 7063, 7673, 7063, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1752];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i, j :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 8815, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 8815);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 8815;
expect forall ii, jj :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 8815;
expect forall jj :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 8815;
}
method {:test} Test2() {
var seqint0 : seq<int> := [0, 2235, 0, -2334, -2335, 0, 0, 0, -2332, 2232, 2234, 0, 0, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i, j :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == -100, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, -100);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == -100;
expect forall ii, jj :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != -100;
expect forall jj :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != -100;
}
method {:test} Test3() {
var seqint0 : seq<int> := [11239, 0, 0, 0, -5218, 0, 0, 0, 0, 0, 0, 0, 0, -11139, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11239, 5318];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i, j :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 100);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 100;
expect forall ii, jj :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 100;
expect forall jj :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 100;
}
method {:test} Test4() {
var seqint0 : seq<int> := [0, 535, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 536, 0, 537, 0, 537, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 536];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i, j :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 1072, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 1072);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 1072;
expect forall ii, jj :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 1072;
expect forall jj :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 1072;
}
method {:test} Test5() {
var seqint0 : seq<int> := [-2332, 3654, -1796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4190, -2332];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i, j :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 1858, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 1858);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 1858;
expect forall ii, jj :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 1858;
expect forall jj :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 1858;
}
method {:test} Test7() {
var seqint0 : seq<int> := [1796, 8365];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i, j :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 10161, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 10161);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 10161;
expect forall ii, jj :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 10161;
expect forall jj :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 10161;
}
method {:test} Test8() {
var seqint0 : seq<int> := [9114, 9725, 9115, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9115, 0, 0, 9724];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i, j :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 18839, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 18839);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 18839;
expect forall ii, jj :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 18839;
expect forall jj :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 18839;
}
method {:test} Test9() {
var seqint0 : seq<int> := [0, 4125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2905, 0, 0, 0, 0, 0, 0, 0, 0, 14715, 2905, 0, 0, 0, 0, 0, 0, 15935, 0, 0, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i: int, j: int {:trigger seqint0[j], seqint0[i]} :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 18840, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 18840);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 18840;
expect forall ii: int, jj: int {:trigger seqint0[jj], seqint0[ii]} :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 18840;
expect forall jj: int {:trigger seqint0[jj]} :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 18840;
}
method {:test} Test10() {
var seqint0 : seq<int> := [0, 16984, 1857, 1321, 1321, 17520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i: int, j: int {:trigger seqint0[j], seqint0[i]} :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 18841, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 18841);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 18841;
expect forall ii: int, jj: int {:trigger seqint0[jj], seqint0[ii]} :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 18841;
expect forall jj: int {:trigger seqint0[jj]} :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 18841;
}
method {:test} Test11() {
var seqint0 : seq<int> := [0, 27244, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11046, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11046, 0, 0, 0, 11048, 27246, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i: int, j: int {:trigger seqint0[j], seqint0[i]} :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 38292, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 38292);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 38292;
expect forall ii: int, jj: int {:trigger seqint0[jj], seqint0[ii]} :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 38292;
expect forall jj: int {:trigger seqint0[jj]} :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 38292;
}
method {:test} Test12() {
var seqint0 : seq<int> := [37684, 609, 1059, 37234, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36091, 2202, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i: int, j: int {:trigger seqint0[j], seqint0[i]} :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 38293, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 38293);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 38293;
expect forall ii: int, jj: int {:trigger seqint0[jj], seqint0[ii]} :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 38293;
expect forall jj: int {:trigger seqint0[jj]} :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 38293;
}
method {:test} Test13() {
var seqint0 : seq<int> := [39886, 1791, 8430, 0, 9276, -449, 39885, 874, 0, 0, 0, 0, 0, 0, 38562, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -450, 0, 0, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i: int, j: int {:trigger seqint0[j], seqint0[i]} :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 39436, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 39436);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 39436;
expect forall ii: int, jj: int {:trigger seqint0[jj], seqint0[ii]} :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 39436;
expect forall jj: int {:trigger seqint0[jj]} :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 39436;
}
