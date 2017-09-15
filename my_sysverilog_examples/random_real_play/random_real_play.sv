`define TOP random_real_play

module random_real_play;

   real one, two, three, four;
   logic [31:0] float1, float2, float3;
   logic [63:0] double1, double2, double3;
   real 	real1, real2, real3;

   logic [31:0] smthg;

`ifdef USE_SVN_TB_RANDOM_NUMBER
`include "tb_random_number.sv"
`endif

   initial begin
      smthg  = 32'h0033_2222;
      next_random(1'b1,smthg);

      for (int lkj=1;lkj<=2;lkj=lkj+1) begin
	 $display(" ** LOOP NUMBER %0d ***",lkj);

	 case(lkj) 
	   1 : begin
	      $display(" \t\t If three =(two*(2^N)), it seems that mN will be X.");	      
	      one    = 1.2E2;
	      two    = 2.4E2;
	      three  = 3.3E2;
	   end
	 2: begin
	    $display(" \t\t Experiment with these numbers");
	    one 	= 0.5E2;
	    two 	= 0.6E2;
	    three 	= 3.3E2;     
	 end
	 endcase
      
//    pick_random_real (.smallest(), .biggest(), .rNum());
//    pick_random_float(.smallest(), .biggest(), .float_number());

      pick_random_real (.smallest(one), .biggest(two), .rNum(four));
      $display(" real between (%0f) and (%0f) is (%0f)",one,two,four);

      end
   end


`ifndef USE_SVN_TB_RANDOM_NUMBER
// /////////////////////////////////////////////////////////////////////
task next_random;
   input new_seed;
   inout [31:0] new_random_value;
   reg [31:0] 	 new_random_value;
   reg [31:0] 	 internal_seed;
   begin
      if (new_seed) begin
`ifdef RANDOM_SEED
         internal_seed 		  = `RANDOM_SEED;
`else
	 if (new_random_value) begin
            internal_seed  = new_random_value;
	 end else begin
            internal_seed  = 32'hFFFF_FFFF;
	 end
`endif
         $display($time, " %m: Setting Random Seed = 32'h%h", 
                   internal_seed);
      end
      // newRandomValue  = $random(internalSeed);
      new_random_value = caustic_random(internal_seed);
   end
endtask // next_random

// /////////////////////////////////////////////
`define RANDOM_NUMBER_SHIFT 32 // okay to use values are 16, 19, 23, 32
function [31:0]  caustic_random ;
   inout [31:0] a;// current seed
   reg          b, c;
   reg [`RANDOM_NUMBER_SHIFT + 31:0] tmp;
   integer      i;
   begin
      if (!a) begin
         a  = 32'hffff_ffff;
         $display("CausticWarning: %t %m : since current seed is 0; reseting it to 0x%h",
                  $time, a);
	 end

      tmp 		       = {a, `RANDOM_NUMBER_SHIFT'hx};
      for (i = `RANDOM_NUMBER_SHIFT-1; i >= 0; i--) begin
         tmp [i] 	       = tmp[i+1] ^ tmp[i+2] ^ tmp[i+22] ^ tmp[i+32];
      end
      caustic_random[31:0]  = tmp[31:0];
      a 		       = caustic_random;
      a 		       = caustic_random;
   end
endfunction // caustic_random 

// /////////////////////////////////////////////////////////////////////
task random_percent;
   input integer high_range;
   output integer percentage;
   reg [31:0] 	  x;
   begin
      `TOP.next_random(0, x);
      if (high_range) begin
	 percentage  = x % high_range;
      end else begin
	 percentage  = 0;
      end
   end
endtask // random_percent

// /////////////////////////////////////////////////////////////////////
    task pick_random_float;
       input real smallest;
       input real biggest;
       output [31:0] float_number;
       real 	     rNum;
       reg [63:0]    double_number;
       begin
	  pick_random_real (smallest, biggest, rNum);
	  $display($time," %m: :A smallest=%0f biggest=%0f rNum(fl.pt.)=%0f =(dec)%0d  =(bin)%0b",
		   smallest,biggest,rNum,$rtoi(rNum),rNum);	  
	  pick_random_real (1.0E2, 1.1E2, rNum);
	  $display($time," %m: :B smallest=%0f biggest=%0f rNum(fl.pt.)=%0f =(dec)%0d  =(bin)%0b",
		   smallest,biggest,rNum,$rtoi(rNum),rNum);	  
	  double_number  = $realtobits(rNum);
	  float_number[31] = double_number[63];
	  float_number[30:23] = double_number[62:52] - 11'h380;
	  float_number[22:0] = double_number[51:0] >> 29;
       end
    endtask // pick_random_float

// /////////////////////////////////////////////////////////////////////
    task pick_random_real;
      input real smallest;
      input real biggest;
      output real rNum;
      reg [31:0]  X1, X2;
      real        realX, rC, rR;
      real        s, b;
      
      reg         sSm, sBg, sN; // sign
      reg [10:0]  eSm, eBg, eN; // integer
      reg [51:0]  mSm, mBg, mN; // unsigned
      begin
         // get absolute values
         s  = (smallest >= 0.0) ? smallest : -smallest;
         b  = (biggest >= 0.0) ? biggest : -biggest;
         
         if ( s > b ) begin // exchange values
            s  = (biggest >= 0.0) ? biggest : -biggest;
            b = (smallest >= 0.0) ? smallest : -smallest;
         end
         
         next_random(0, X1);
         next_random(0, X2);
	 repeat (1) $display("\t\t lkj two random 32b #s are concatenated to make starting new number: X1=%0h X2=%0h",X1,X2);	 
         {sN, eN, mN} 	  = {X1,X2};
	 repeat (1) $display("\t\t lkj NEW  w/randoms: \t sN =%0b \t eN =%0h \t mN =%0h",sN,eN,mN);
         {sSm, eSm, mSm}  = $realtobits(smallest);
	 repeat (1) $display("\t\t lkj Small input (%0d):\t sSm=%0b \t eSm=%0h \t mSm=%0h",$rtoi(smallest), sSm,eSm,mSm);
         {sBg, eBg, mBg}  = $realtobits(biggest);
	 repeat (1) $display("\t\t lkj Big input (%0d):  \t sBg=%0b \t eBg=%0h \t mBg=%0h",$rtoi(biggest), sBg,eBg,mBg);


         // pick sign
         if ( sSm === sBg ) sN = sSm;
         
         // restrict to range
         {sSm, eSm, mSm}  = $realtobits(s);
         {sBg, eBg, mBg}  = $realtobits(b);
	 eN               = eN % (eBg - eSm) + eSm;
         mN               = mN % (mBg - mSm) + mSm;
/*this will take care of fact that (eBg - eSm) or (mBg - mSm) might ==0, in which case we get an X, however,
 this will still have the issue that numbers which are 2^N of each other will have the same mantissa but a
 difference of +1 in the exponent.  so the new mantissa will be ==mSm==mBg, and the exponent will be the
 only thing that changes
         eN 		  = (eN % ((eBg - eSm)+1)) + eSm;
         mN 		  = (mN % ((mBg - mSm)+1)) + mSm;
*/	 
	 repeat (1) $display("\t\t lkj NEW(in range):\t sN =%0b \t eN =%0h \t mN =%0h ",sN,eN,mN);
	 
         // convert back to real
         rNum 		  = $bitstoreal ( {sN, eN, mN} );
         
      end
   endtask // pick_random_real

`endif

endmodule






