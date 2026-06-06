// dafny-language-server_tmp_tmpkir0kenl_Test_dafny0_snapshots_Inputs_Snapshots0.dfy

method {:testEntry} foo()
{
  bar();
  assert false;
}

method {:testEntry} bar()
  ensures false
