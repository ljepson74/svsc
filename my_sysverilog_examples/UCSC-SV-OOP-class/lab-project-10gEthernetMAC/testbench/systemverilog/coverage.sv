//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

//Collect functional coverage to see if we have the full range of modulus
//packet sizes.  Coverage for how that compares across different packet
//sizes.
//ToDo: Add more interesting coverage, as well as coverage internal to DUT.

class coverage;

   packet covpacket;

   covergroup cg_projectcov;
      cp_tx_length: coverpoint covpacket.tx_length{
         bins mini  ={[64:100]};
         bins mid   ={[100:8000]};
         bins big   ={[8000:9000]};
         bins other =default;
      }

      cp_tx_mod: coverpoint covpacket.tx_mod;

      cp_length_x_mod: cross cp_tx_length, cp_tx_mod;
   endgroup : cg_projectcov

     function new();
        cg_projectcov = new();
     endfunction : new

   task collect_coverage(input packet get_cov_pkt);
      this.covpacket = get_cov_pkt;
      cg_projectcov.sample();
   endtask : collect_coverage

endclass : coverage
