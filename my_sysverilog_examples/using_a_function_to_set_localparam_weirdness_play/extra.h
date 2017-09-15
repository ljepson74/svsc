/*
function integer clogb2 (input integer depth);
  integer     offset;
  integer     cloop;

  
      offset=1;

      for(cloop=0; depth>0; cloop=cloop+1) begin
	 if (depth[0] & depth != 1)  // not a power of 2
	    offset=0;
         depth = depth >> 1;
      end
      clogb2 = cloop-offset;
endfunction
*/

function integer clogb2 (input integer depth);
  integer     offset;
  integer     cloop;

  
      offset=1;

      $display(" WE ARE IN");
      $display("WHY IS THIS IGNORED?  b/c the function is being run at time=0.  hmmm. I guess that makes sense to me, in some regard.");
      $display("However, since it was run, I would expect it to be executed.");
      $finish;

      for(cloop=0; depth>0; cloop=cloop+1) begin
	 if (depth[0] & depth != 1)  // not a power of 2
	    offset=0;
         depth = depth >> 1;
      end
      clogb2 = cloop-offset;
endfunction
