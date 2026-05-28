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
      if i != j {
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
var seqreal0 : seq<real> := [8856.0, 0.0];
var r0 := has_close_elements(seqreal0, 8857.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 8857.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test2() {
var seqreal0 : seq<real> := [0.0, -(108609.0 / 1250.0)];
var r0 := has_close_elements(seqreal0, 100.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 100.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test5() {
var seqreal0 : seq<real> := [0.0, -2438.0];
var r0 := has_close_elements(seqreal0, 2439.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 2439.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test6() {
var seqreal0 : seq<real> := [0.0, 8856.0];
var r0 := has_close_elements(seqreal0, 8857.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 8857.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test7() {
var seqreal0 : seq<real> := [];
var r0 := has_close_elements(seqreal0, 0.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 0.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test9() {
var seqreal0 : seq<real> := [0.0];
var r0 := has_close_elements(seqreal0, 0.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 0.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test10() {
var seqreal0 : seq<real> := [0.0, 0.0];
var r0 := has_close_elements(seqreal0, 0.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 0.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test11() {
var seqreal0 : seq<real> := [];
var r0 := has_close_elements(seqreal0, -100.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < -100.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test12() {
var seqreal0 : seq<real> := [];
var r0 := has_close_elements(seqreal0, 100.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 100.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test17() {
var seqreal0 : seq<real> := [-(12837.0 / 2.0), 2437.0, 609.0];
var r0 := has_close_elements(seqreal0, 35425.0/2.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 35425.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test18() {
var seqreal0 : seq<real> := [-(42405005232440086877374954911.0 / 625000000000000000000000.0), 2437.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(1042362630653740506808309.0 / 62500000000000000000.0), 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(18137461013812413471323711637.0 / 625000000000000000000000.0), -(27376117504703195784513711637.0 / 625000000000000000000000.0), -(17253718184285820665472166637.0 / 312500000000000000000000.0), -(4277487400827895546430621637.0 / 625000000000000000000000.0)];
var r0 := has_close_elements(seqreal0, 5707568863868445546430621637.0/625000000000000000000000.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 5707568863868445546430621637.0/625000000000000000000000.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test19() {
var seqreal0 : seq<real> := [2211.0, 1594.0, 8221.0, -(29854133.0 / 4000.0), 582.0, 1108.0];
var r0 := has_close_elements(seqreal0, 35427.0/2.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 35427.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test20() {
var seqreal0 : seq<real> := [68575.0 / 2.0, 7719.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 53137.0/2.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 53137.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test21() {
var seqreal0 : seq<real> := [8456.0, 10240629.0 / 800.0, 8879.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2240.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1323.0];
var r0 := has_close_elements(seqreal0, 53139.0/2.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 53139.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test22() {
var seqreal0 : seq<real> := [3212.0, 125330.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 189601.0 / 2.0, 0.0, 0.0, 0.0, 64271.0, 67483.0 / 2.0, -(54635.0 / 2.0), -57847.0, 0.0];
var r0 := has_close_elements(seqreal0, 61059.0/2.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 61059.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test23() {
var seqreal0 : seq<real> := [5981.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 334.0, 0.0, 3960.0, 238968963.0 / 10000.0, 6019.0, 1391.0, 624.0, 7065.0];
var r0 := has_close_elements(seqreal0, 61061.0/2.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 61061.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test24() {
var seqreal0 : seq<real> := [1323.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 77463.0 / 2.0, -(72171.0 / 2.0), -73494.0];
var r0 := has_close_elements(seqreal0, 74817.0/2.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 74817.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test25() {
var seqreal0 : seq<real> := [39276113.0 / 1000.0, 8586.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1235.0, 0.0, 0.0, 0.0, 0.0, 0.0, 6906.0, 3609.0, 2616.0];
var r0 := has_close_elements(seqreal0, 74819.0/2.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 74819.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test26() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 107967.0 / 2.0, 0.0, 0.0, 0.0, 7719.0];
var r0 := has_close_elements(seqreal0, 92529.0/2.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 92529.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test27() {
var seqreal0 : seq<real> := [201962877.0 / 5000.0, 2437.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 92531.0/2.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 92531.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test28() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 1.0);
expect r0 <==> exists i: int, j: int {:trigger seqreal0[j], seqreal0[i]} :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 1.0;
expect r0 ==> |seqreal0| > 1;
}
