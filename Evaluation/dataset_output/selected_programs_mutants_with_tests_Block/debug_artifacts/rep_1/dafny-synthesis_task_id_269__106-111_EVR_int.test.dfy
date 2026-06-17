// dafny-synthesis_task_id_269.dfy

method {:testEntry} AsciiValue(c: char) returns (ascii: int)
  ensures ascii == c as int
{
  ascii := 0;
}

method {:test} Test0() {
var r0 := AsciiValue('&');
expect r0 == '&' as int;
}

// REPEAT 1 - TIME: 2.1368883 s
