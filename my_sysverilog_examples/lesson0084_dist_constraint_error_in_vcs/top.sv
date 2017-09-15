module top;

class classact;
   int v1;
   rand int v2;

   //v1
//   constraint c_1 {(v1==11) || (v1==101);}    //1 VCS
//   constraint c_2 {v1==22;}                   //2 VCS
     constraint c_3 {v1 dist {0:/11, 1:/22}; }  //3 noVCS
//   constraint c_4 {v1 inside {0,1, [22:23]};} //4 VCS

   //v2
//   constraint c_5 {v2==22;}                   //VCS

   function void post_randomize();
      $display("result: v1=%0d  v2=%0d",v1,v2);
   endfunction
endclass


   classact a_classact;
   
   initial begin
      repeat (3) $display(" WELCOME ");
      a_classact=new();
//ignore      assert(a_classact.randomize());
   end
endmodule // top
