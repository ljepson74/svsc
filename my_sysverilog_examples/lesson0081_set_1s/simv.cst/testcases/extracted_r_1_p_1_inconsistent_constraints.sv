class c_1_1;
    rand bit[3:0] muggle; // rand_mode = ON 

    constraint WITH_CONSTRAINT_this    // (constraint_mode = ON) (top.sv:20)
    {
       (muggle == (-1));
    }
endclass

program p_1_1;
    c_1_1 obj;
    string randState;

    initial
        begin
            obj = new;
            randState = "z11xzxx10xz01z1z100z10x01xx01z1zxxxxxxzxzzzzzxzxzxxxxzxzzzzzxzxz";
            obj.set_randstate(randState);
            obj.randomize();
        end
endprogram
