//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

package tasks;  //tasks and functions
   integer       tx_length;
   int           err_cnt;

   task WaitNS;
      input [31:0] delay;

      #(1000*delay);
   endtask

   task WaitPS;
      input [31:0] delay;

      #(delay);
   endtask

   function void printme(input string note1="asdf", input string note2="fdsa");
      $display($time,":lkj:: %0s:%0s",note1,note2);
   endfunction : printme

   function void set_err_cnt(input int value=0);
      err_cnt = value;
   endfunction : set_err_cnt

   function void inc_err_cnt();
      err_cnt++;
   endfunction : inc_err_cnt

   function int get_err_cnt();
      return(err_cnt);
   endfunction : get_err_cnt
endpackage : tasks
