// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 0 <= i < |s|;
  count := |uppercase|;
}

method {:test} Test4() {
var r0 := CountUppercase("a\0aGa");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 6.2903567 s
