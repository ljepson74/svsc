

/*
 An example to demonstrate how bidirectional constraints work in SV.
 Note that this is not a good example to demonstrate UVM nor class based verification.
*/



module test_sv_birectional_constraints;

    class ClassE;
        rand bit[3:0] mode_len;
        rand bit a, b;
        string name;

        function new (string name = "");
            this.name = name;
        endfunction

        function void post_randomize;
            $display("name = '%s', a = '%1b', b = '%1b', len = '%1d'", name, a, b, mode_len);
        endfunction

        // if a is same as b then mode_len should be 10
        constraint c_mode_e {
            (a == b) -> (mode_len == 10);
        }

    endclass


    initial begin
        ClassE obj_ab;
        int unsigned repeat_count;
        
        repeat_count = 20;
        obj_ab = new("obj_ab");

        $display("\ninline constrains with a==b, Point 1 -- LHS True, then RHS should be True");
        repeat(repeat_count) begin
           if (! obj_ab.randomize() with {a == b;}) begin
                $display("obj_ab randomization failed");
            end else begin
                if (obj_ab.mode_len != 10) begin
                    $display("Warning: obj_ab.mode_len is not 10, when a==b");
                end
            end
        end

        $display("\ninline constrains with a!=b, Point 2 -- LHS False, then RHS is unconstrained");
        repeat(repeat_count) begin
           if (! obj_ab.randomize() with {a != b;}) begin
                $display("obj_ab randomization failed");
            end
        end

        $display("\ninline constrains with len == 10, Point 3 -- RHS True, then LHS unconstrained");
        repeat(repeat_count) begin
            if (! obj_ab.randomize() with {mode_len == 10;} ) begin
                $display("obj_ab randomization failed");
            end
        end

        $display("\ninline constrains with len != 10, Point 4 -- RHS False, then LHS should be False");
        repeat(repeat_count) begin
           if (! obj_ab.randomize() with {mode_len != 10;}) begin
                $display("obj_ab randomization failed");
            end else begin
                if (obj_ab.a == obj_ab.b) begin
                    $display("Warning: obj_ab  a and b are equal, len is not 10");
                end
            end
        end
        
        $display("\nNo inline constrains");
        repeat(repeat_count*4) begin
            if (! obj_ab.randomize() ) begin
                $display("obj_ab randomization failed");
            end
        end
        
        $display("\ninline constrains solve before");
        repeat(repeat_count) begin
            if (! obj_ab.randomize() with {solve a before mode_len; solve b before mode_len;}) begin
                $display("obj_ab randomization failed");
            end
        end

    end

endmodule

// run with
// irun -c -sv test_sv_birectional_constraints.sv && do.grid -mem 2000 --l Incisive_Enterprise_Simulator -jobname irunsv -do irun -sv test_sv_birectional_constraints.sv -run


