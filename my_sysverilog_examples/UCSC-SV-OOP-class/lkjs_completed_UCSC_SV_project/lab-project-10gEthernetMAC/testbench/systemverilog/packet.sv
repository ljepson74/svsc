//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

import tasks::*;
class packet;
   string where="pkt";

   protected static int total_driven;
   protected static int total_collected;
   static int           total_number;

   rand logic [2:0] tx_mod;
   rand logic [7:0] tx_data[];//lkj just call this data, since it goes both ways
   rand integer     tx_length;//is this needed?

   rand bit         sop;  //rand so sometimes drop it
   rand bit         eop;  //rand so sometimes drop it
   rand int         ipg;

   constraint c_ipg { ipg dist {0      :/ 70,
                                [1:30] :/ 30};
                     }

   constraint c_tx_data_size {
      tx_data.size() dist {[64:80]    :/ 45,
                           [81:9850]  :/  3,
                           [9850:9899]:/ 45
                           };
   }

   constraint c_legal_sop { sop==1'b1;}
   constraint c_legal_eop { eop==1'b1;}

   extern function new(input string name="sam");

   extern function void post_randomize();
   extern function void add8B(input logic [63:0] data);
   extern function void show(input string note="");
   extern function int  len();
   extern function int  compare(input packet other1);
   extern function void adjust_for_mod();
   extern static function void inc_total_driven();
   extern static function void inc_total_collected();
   extern static function int  get_total_driven();
   extern static function int  get_total_collected();
endclass : packet

///
///
///

function packet::new(input string name="sam");
   tx_length=0;
endfunction : new

function void packet::show(input string note=""); //lkj note not used
   string datastring="";
   where = {note,where};

   tx_length = tx_data.size();
   size_chk : assert (tx_length==tx_data.size()) else begin
      printme(where,
              $psprintf("ERROR. sizes mismatch. tx_length(%0d)!=tx_data.size()(%0d)",
                        tx_length,tx_data.size()));
      $finish;
   end
   //printme(where,"---------------------------------------------------------");
   datastring=$psprintf(" size=%0d mod=%3b\n", tx_data.size(),tx_mod);

   for (int jj=1; (jj<=tx_length) && (jj<100); jj++) begin
      datastring={datastring, $psprintf(" %2x",tx_data[jj-1])}; //jj-1, b/c start count from jj=1
      if ( (jj>0) && ((jj%8)==0) ) begin
         datastring={datastring,"\n"};
      end
      if (jj==99) begin
         datastring={datastring,"\nBig packet (>99) truncated view."};
      end
   end

    datastring={datastring,"\n"};
   printme(where,datastring);
   //printme(where,"---------------------------------------------------------");
endfunction : show


//used by monitor when adding data to packet
function void packet::add8B(input logic [63:0] data);
   string msg="";

   tx_length = tx_data.size();
   msg = $psprintf("adding to packet. size=%0d to =",tx_data.size());

   //increase size by 8B, perserve existing data (tx_data)
   tx_data   = new[ (tx_length+8) ](tx_data);
   //printme(where,$psprintf("%0s%0d",msg,tx_data.size()));
   tx_length = tx_data.size();

   //assign newly collected data
   tx_data[(tx_length-1)] = data[`LANE0];
   tx_data[(tx_length-2)] = data[`LANE1];
   tx_data[(tx_length-3)] = data[`LANE2];
   tx_data[(tx_length-4)] = data[`LANE3];
   tx_data[(tx_length-5)] = data[`LANE4];
   tx_data[(tx_length-6)] = data[`LANE5];
   tx_data[(tx_length-7)] = data[`LANE6];
   tx_data[(tx_length-8)] = data[`LANE7];
endfunction : add8B


function void packet::post_randomize();
   tx_length = tx_data.size();
   tx_mod    = (tx_data.size()%8);
endfunction : post_randomize


function void packet::adjust_for_mod();
   int num_to_remove=0;
   logic [7:0] temp[]; //what is better way to delete element from dyn array?

   //after filling packet with data, if mod!=0, then we want to remove
   //excess bytes
   //if mod==0, we dont remove anything from the last 8B
   //if mod==1, we want to keep 1 of last 8B and remove 7B
   //if mod==2, we want to keep 2 of last 8B and remove 6B
   //if mod==7, we want to keep 7 of last 8B and remove 1B
   if ( int'(tx_mod) ) begin
     num_to_remove = ( 8 - int'(tx_mod) );
      //$display("tx_data.size()=%0d",tx_data.size());
      temp = new[ (tx_data.size()-num_to_remove) ](tx_data);
      tx_data = temp;
      //$display("tx_data.size()=%0d",tx_data.size());
   end
endfunction : adjust_for_mod


function int packet::len();
   return(tx_data.size());
endfunction : len


function int packet::compare(input packet other1);
   bit err=0;

   printme(where,$psprintf(" ******PACKET COMPARE #%0d****** ",get_total_collected()));

   if (this.tx_data.size() == other1.tx_data.size()) begin
      printme(where,$psprintf("  Both have data size (Bytes) = %0d",this.tx_data.size()));
   end else begin
      printme(where,$psprintf("ERROR: Both have different data sizes (Bytes)  (%0s):%0d  (%0s):%0d",
                              this.where,   this.tx_data.size(),
                              other1.where, other1.tx_data.size()));
      err=1'b1;
   end

   for (int gg=0; (gg<this.tx_data.size()) && (err==1'b0); gg++) begin
      if (this.tx_data[gg] == other1.tx_data[gg]) begin
         //printme(where,$psprintf("tx_data match for Byte#%0d (Byte=%2x)",gg,this.tx_data[gg]));
      end else begin
         printme(where,$psprintf("ERROR: tx_data mismatch for Byte#%0d (Byte %2x!=%2x)",
                                 gg,this.tx_data[gg],other1.tx_data[gg]));
         err=1'b1;
      end
   end

   if (err==1'b1) begin inc_err_cnt(); end
endfunction : compare


static function void packet::inc_total_driven();
   total_driven++;
endfunction : inc_total_driven

static function void packet::inc_total_collected();
   total_collected++;
endfunction : inc_total_collected

static function int  packet::get_total_driven();
   return(total_driven);
endfunction : get_total_driven

static function int  packet::get_total_collected();
   return(total_collected);
endfunction : get_total_collected
