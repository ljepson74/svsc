//This example was taken from ---somewhere I cant recall--- and modified
// It is intended to indicate bidirectional constraints.

module top();

class myclass;
   rand bit[1:0] mode_len;
   rand bit      a, b;
   string        name;

   function new (string name = "");
      this.name = name;
   endfunction

   function void post_randomize;
      $display("a=%1b, b=%1b, len=%1d", a, b, mode_len);
   endfunction

   // if a is same as b then mode_len should be 2
   constraint c_mode_e { (a == b) -> (mode_len == 2'd2); }
endclass : myclass

   //
   //
   //

   initial begin
      myclass obj_ab;
      int unsigned repeat_count;

      repeat_count = 10;
      obj_ab = new("obj_ab");

      $display("\ninline constraints with a==b, Point 1 -- LHS True, then RHS should be True");
      repeat(repeat_count) begin
         if (! obj_ab.randomize() with {a == b;}) begin
            $display("obj_ab randomization failed");
         end else begin
            if (obj_ab.mode_len != 2'd2) begin
               $display("Warning: obj_ab.mode_len is not 2'd2, when a==b");
            end
         end
      end

      $display("\ninline constraints with a!=b, Point 2 -- LHS False, then RHS is unconstrained");
      repeat(repeat_count) begin
         if (! obj_ab.randomize() with {a != b;}) begin
            $display("obj_ab randomization failed");
         end
      end

      $display("\ninline constraints with len == 2'd2, Point 3 -- RHS True, then LHS unconstrained");
      repeat(repeat_count) begin
         if (! obj_ab.randomize() with {mode_len == 2'd2;} ) begin
            $display("obj_ab randomization failed");
         end
      end

      $display("\ninline constraints with len != 2'd2, Point 4 -- RHS False, then LHS should be False");
      repeat(repeat_count) begin
         if (! obj_ab.randomize() with {mode_len != 2'd2;}) begin
            $display("obj_ab randomization failed");
         end else begin
            if (obj_ab.a == obj_ab.b) begin
               $display("Warning: obj_ab  a and b are equal, len is not 2'd2");
            end
         end
      end

      $display("\nNo inline constraints");
      repeat(repeat_count*2) begin
         if (! obj_ab.randomize() ) begin
            $display("obj_ab randomization failed");
         end
      end

      $display("\ninline constraints solve before");
      repeat(repeat_count) begin
         if (! obj_ab.randomize() with {solve a before mode_len; solve b before mode_len;}) begin
            $display("obj_ab randomization failed");
         end
      end

   end
endmodule : top

// run with "go"
