function abs(x: real): real
{
  if x < 0.0 then -x else x
}

method {:testEntry} has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    ensures result <==> exists i, j ::
      0 <= i < |numbers| &&
      0 <= j < |numbers| &&
      i != j &&
      abs(numbers[i] - numbers[j]) < threshold
    ensures result ==> |numbers| > 1
{
    result := false;

    assert (forall i0 :: (0 <= i0 < 0 ==>
                   forall j0 :: (0 <= j0 < |numbers| ==>
                   abs(numbers[i0] - numbers[j0]) >= threshold)));

    for i := 0 to |numbers|
        invariant (forall i0 :: (0 <= i0 < i ==>
                   forall j0 :: (0 <= j0 < |numbers| ==>
                   (i0 != j0 ==>
                   abs(numbers[i0] - numbers[j0]) >= threshold))))
    {
        for j := 0 to |numbers|
             invariant (forall i0 :: (0 <= i0 <= i ==>
                        forall j0 :: (0 <= j0 < j ==>
                        (i0 != j0 ==>
                        abs(numbers[i0] - numbers[j0]) >= threshold))))
        {
            if i != j && abs(numbers[i] - numbers[j]) < threshold {
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

// REPEAT 1 - TIME: 9.4655638 s

method {:test} Test17() {
var seqreal0 : seq<real> := [-(12837.0 / 2.0), 2437.0, 609.0];
var r0 := has_close_elements(seqreal0, 35425.0/2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 35425.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test18() {
var seqreal0 : seq<real> := [-(42405005232440086877374954911.0 / 625000000000000000000000.0), 2437.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(1042362630653740506808309.0 / 62500000000000000000.0), 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(18137461013812413471323711637.0 / 625000000000000000000000.0), -(27376117504703195784513711637.0 / 625000000000000000000000.0), -(17253718184285820665472166637.0 / 312500000000000000000000.0), -(4277487400827895546430621637.0 / 625000000000000000000000.0)];
var r0 := has_close_elements(seqreal0, 5707568863868445546430621637.0/625000000000000000000000.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 5707568863868445546430621637.0/625000000000000000000000.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 2 - TIME: 10.6098496 s

method {:test} Test19() {
var seqreal0 : seq<real> := [5904.0, 1323.0, 102177573.0 / 5000.0, 8456.0, 8879.0];
var r0 := has_close_elements(seqreal0, 35427.0/2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 35427.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test20() {
var seqreal0 : seq<real> := [2282.0, 37709.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 39991.0 / 2.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(30863.0 / 2.0)];
var r0 := has_close_elements(seqreal0, 35427.0/2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 35427.0/2.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 3 - TIME: 11.8703696 s

method {:test} Test21() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 7065.0, -(14523.0 / 2.0), 1594.0, 582.0, 2211.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7578.0, 1108.0];
var r0 := has_close_elements(seqreal0, 26569.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 26569.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test22() {
var seqreal0 : seq<real> := [47568844657724087.0 / 312500000000.0, 0.0, 0.0, 116543109416763511.0 / 1250000000000.0, 36915932305587837.0 / 312500000000.0, 49875619805587837.0 / 1250000000000.0, 41531244805587837.0 / 625000000000.0, 6906.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 31120619805587837.0/1250000000000.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 31120619805587837.0/1250000000000.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 4 - TIME: 13.0192139 s

method {:test} Test23() {
var seqreal0 : seq<real> := [5379.0, 7176.0, 4135.0, 0.0, 0.0, 9263.0, 6926.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2112.0, 1102.0];
var r0 := has_close_elements(seqreal0, 28366.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 28366.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test24() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 1.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 1.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 5 - TIME: 14.4103104 s

method {:test} Test25() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 531.0, 4186.0, 13728823.0 / 500.0, 6019.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 3023.0, 8935.0, 1573.0];
var r0 := has_close_elements(seqreal0, 28367.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 28367.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test26() {
var seqreal0 : seq<real> := [890830442427764911754943210527808443832669006702047.0 / 12207031250000000000000000000000000000000000000.0, 409343663952115246789276731143251084934715766331409.0 / 12207031250000000000000000000000000000000000000.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1028715177718356806481664812730920076500393616077047.0 / 6103515625000000000000000000000000000000000000.0, 0.0, 0.0, 1673996024748616523181310651533602001077648862486141.0 / 12207031250000000000000000000000000000000000000.0, 644079107980665995709510578749720758806816099767047.0 / 6103515625000000000000000000000000000000000000.0, 867.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 347698495879727459646438663956035483464016662952047.0/12207031250000000000000000000000000000000000000.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 347698495879727459646438663956035483464016662952047.0/12207031250000000000000000000000000000000000000.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 6 - TIME: 15.7035706 s

method {:test} Test27() {
var seqreal0 : seq<real> := [449.0, -(604814917550653581033842873866138841214773510088075237.0 / 24414062500000000000000000000000000000000000000000.0), 609.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 347710702910977459646438663956035483464016662952047.0/12207031250000000000000000000000000000000000000.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 347710702910977459646438663956035483464016662952047.0/12207031250000000000000000000000000000000000000.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test28() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 3.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 3.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 7 - TIME: 16.9193445 s

method {:test} Test29() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 8855.0, 114086012068752370618749039883740067924656518334530897.0 / 30517578125000000000000000000000000000000000000000.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 347722909942227459646438663956035483464016662952047.0/12207031250000000000000000000000000000000000000.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 347722909942227459646438663956035483464016662952047.0/12207031250000000000000000000000000000000000000.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test30() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 4.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 4.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 8 - TIME: 18.2528525 s

method {:test} Test31() {
var seqreal0 : seq<real> := [-(25673.0 / 4.0), 2437.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 455819223418789959646438663956035483464016662952047.0/12207031250000000000000000000000000000000000000.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 455819223418789959646438663956035483464016662952047.0/12207031250000000000000000000000000000000000000.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test32() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 5.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 5.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 9 - TIME: 19.4286347 s

method {:test} Test33() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1796.0, -(718741896228854352488491884798447363835299877118774631.0 / 24414062500000000000000000000000000000000000000000.0), 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 455831430450039959646438663956035483464016662952047.0/12207031250000000000000000000000000000000000000.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 455831430450039959646438663956035483464016662952047.0/12207031250000000000000000000000000000000000000.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test34() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 6.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 6.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 10 - TIME: 20.6096066 s
