// llm-verified-eval_tmp_tmpd2deqn_i_dafny_0.dfy

function abs(x: real): real
{
  if x < 0.0 then
    -x
  else
    x
}

method {:testEntry} has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
  ensures result <==> exists i, j :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold
  ensures result ==> |numbers| > 1
{
  result := false;
  assert forall i0 :: 0 <= i0 < 0 ==> forall j0 :: 0 <= j0 < |numbers| ==> abs(numbers[i0] - numbers[j0]) >= threshold;
  for i := 0 to |numbers|
    invariant forall i0 :: 0 <= i0 < i ==> forall j0 :: 0 <= j0 < |numbers| ==> i0 != j0 ==> abs(numbers[i0] - numbers[j0]) >= threshold
  {
    for j := 0 to |numbers|
      invariant forall i0 :: 0 <= i0 <= i ==> forall j0 :: 0 <= j0 < j ==> i0 != j0 ==> abs(numbers[i0] - numbers[j0]) >= threshold
    {
      if false {
        assert abs(numbers[i] - numbers[j]) < threshold;
        result := true;
        return;
      }
    }
  }
}

method {:test} Test0() {
var seqreal0 : seq<real> := [-2438.0, 0.0];
var r0 := has_close_elements(seqreal0, 2439.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 2439.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test1() {
var seqreal0 : seq<real> := [];
var r0 := has_close_elements(seqreal0, 0.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 0.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test2() {
var seqreal0 : seq<real> := [8098.0, 1796.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2195613.0 / 1000.0];
var r0 := has_close_elements(seqreal0, 2440.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 2440.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test3() {
var seqreal0 : seq<real> := [0.0];
var r0 := has_close_elements(seqreal0, 1.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 1.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test4() {
var seqreal0 : seq<real> := [27142389.0 / 2500.0, 8855.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 2441.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 2441.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test5() {
var seqreal0 : seq<real> := [-4544.0, 1236.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -1654.0];
var r0 := has_close_elements(seqreal0, 2890.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 2890.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test6() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 6789.0, 8586.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1235.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 6906.0, 3609.0, 2616.0];
var r0 := has_close_elements(seqreal0, 4687.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 4687.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test7() {
var seqreal0 : seq<real> := [17109.0, 8365.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -379.0];
var r0 := has_close_elements(seqreal0, 8744.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 8744.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test8() {
var seqreal0 : seq<real> := [7629.0, 7578.0, 2379.0, 2211.0, 0.0, 0.0, 1108.0, 582.0, 0.0, 7065.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 10541.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 10541.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test9() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 55955.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 44932.0, 33909.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 22886.0, 11863.0, 840.0, 0.0];
var r0 := has_close_elements(seqreal0, 11023.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 11023.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test10() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 6048.0, 5968.0, 7523.0, 5045.0, 17790561.0 / 1250.0, 5189.0, 8746.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 9619.0, 6333.0, 0.0, 0.0, 119.0, 3577.0];
var r0 := has_close_elements(seqreal0, 11024.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 11024.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test11() {
var seqreal0 : seq<real> := [24065.0 / 2.0, 24384.0, 12301.0, 9402.0, 21171.0, 4718.0, -1224.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, -1.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < -1.0;
expect r0 ==> |seqreal0| > 1;
}
