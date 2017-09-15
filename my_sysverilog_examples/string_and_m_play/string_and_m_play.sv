

module string_and_m_play;


   initial
     begin
	cgmsg(0,"are you getting this?",%m);
     end



   function void cgmsg(); ////cgmsg = caustic graphics message
      input int level;
      input string msg_string;
      input string hier;
      
      //   string    msg_string;

      case (level)
	0   :
	  begin
	     $display("NOTE: %s.  we are here %s",msg_string, hier); 
	  end
	10  :
	  begin
	     //	  $display("MSG: %s",msg_string);	  
	     $display("MSG lincoln:");	  
	  end
	20  :
	  begin
	     $display("WARNING: %s",msg_string);	  
	  end       
	30  :
	  begin	  
	     $display("ERROR: %s",msg_string);
	  end
      endcase // case unique

   endfunction
   
endmodule // string_and_m_play


