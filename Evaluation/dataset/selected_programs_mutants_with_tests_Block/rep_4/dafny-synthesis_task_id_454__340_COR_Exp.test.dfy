// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] == 'z' <== s[i] == 'Z' {
      result := true;
      break;
    }
  }
}

method {:test} Test6() {
var r0 := ContainsZ("\U{0001}aZaaaaaaaaaaaaa\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}aZaaaaaaaaaaaaa\U{0003}"| && ("\U{0001}aZaaaaaaaaaaaaa\U{0003}"[i] == 'z' || "\U{0001}aZaaaaaaaaaaaaa\U{0003}"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("\U{0001}za\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}za\U{0003}"| && ("\U{0001}za\U{0003}"[i] == 'z' || "\U{0001}za\U{0003}"[i] == 'Z');
}

// REPEAT 4 - TIME: 6.946813 s
