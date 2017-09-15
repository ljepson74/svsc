// Goals:
//  *) Extend class and tb-owner defines +args
//     Checks:
//  *)   +args must be defined : error (avoids typos) 
//  *)   +args may be used only once : error (avoids duplicates)
//  *)

import uvm_pkg::*;
`include "iclp_pkg.svh"
`include "iplusarg.svh"
`include "uvm_macros.svh"
import iclp_pkg::*;
class iclp extends uvm_component;
   string where="iclp";
   string verb =UVM_LOW;

   uvm_cmdline_processor uclp;


   plusarg nupa[string];  //nupa - Non-UVM PlusArgs (i.e. not +UVM_VERBOSITY
   
   string all_arg_values[$];
   string some_arg_values[$];

   bit    plusargs_bit[string];
   int    plusargs_int[string];
   string plusargs_string[string];

   //protected to require they be accessed via methods
   protected string possible_args[$];
   protected string possible_desc[$];

   `uvm_component_utils(iclp)

   function new(string name="iclp", uvm_component parent = null);
      super.new(name,parent);
      `uvm_info(where,"calling new inside iclp",verb)
      uclp=uvm_cmdline_processor::get_inst();
   endfunction : new

   //phase methods
   extern function void build_phase(uvm_phase phase);
   extern function void connect_phase(uvm_phase phase);
   extern function void end_of_elaboration_phase(uvm_phase phase);

   //other methods
   extern function void add_plusarg(input valuetype_e valtype,
                                      input string arg, input string desc,
                                      input int dflt=0, input string dflt_s="");
   extern function int  get_arg_values (string match, ref string values[$]);

   extern function void show_all_legal_plusarg_options(input string note="");
   extern function void show_all_received_plusargs(input string note="");
   extern function void check_all_received_plusargs_are_legal();
   extern function bit  check_non_uvm_plusarg_is_legal(input string arg);
   extern function void update_plusarg_values();
   extern function void print_separator(input string string1, input string string2, input int my_verb=verb);
   extern function void confirm_bool(input string name, input int val);
   extern function void confirm_one_or_die(input int size, input string name);
   extern function void show_all_final_values();
   extern function int    add_plusarg_int(   input string name, input string desc, input int default_val);
   extern function string add_plusarg_string(input string name, input string desc, input string default_val);
   
   extern function string remove_all_after_equal(input string string1);
   extern function bit    b(input string arg);
   extern function int    i(input string arg);
   extern function string s(input string arg);
endclass : iclp

///
///
///

//10. Get all input plusargs
//20. Show all input plusargs
function void iclp::build_phase(uvm_phase phase);
   repeat (1) `uvm_info(where,"***BUILD***.",UVM_HIGH)
   uclp.get_plusargs(all_arg_values); //10.
   show_all_received_plusargs();  //20.
endfunction : build_phase

function void iclp::connect_phase(uvm_phase phase);
endfunction : connect_phase

//30. Show all legal (allowed) options to stdout
//40. check 'all' +args are legal (ignore assignment values)
//50. show all +arg final values.  indicate if it was used
function void iclp::end_of_elaboration_phase(uvm_phase phase);
   show_all_legal_plusarg_options();        //30.
   check_all_received_plusargs_are_legal(); //40.
   show_all_final_values();                 //50.
endfunction : end_of_elaboration_phase


//
//

function void iclp::add_plusarg(input valuetype_e valtype,
                                  input string arg, input string desc,
                                  input int dflt=0, input string dflt_s="");
   string where="add_plusarg_and_override";
   string results="";
   int verb = UVM_DEBUG;
   
   //input string desc="-blank-");
   `uvm_info(where,$psprintf("LEGAL ARGS: %0s",arg),verb)
   possible_args.push_back(arg);
   possible_desc.push_back(desc);

   //This should be broken up.  i.e. store originals
   case (valtype)
     BIT : begin
        `uvm_info(where,$psprintf("BIT: arg=%0s. val=%0d",arg,dflt),verb)
        confirm_bool(arg,dflt);
        plusargs_bit[arg]=dflt;
	results = $psprintf("bit plusarg name is: %0s. ",arg);
	if (uclp.get_arg_values(.match(arg), .values(some_arg_values))) begin
	   confirm_one_or_die(some_arg_values.size(), arg);
	   results = {results, $psprintf("new-val:%0d \t\t //Overridden.",some_arg_values[0].atoi()) };
	   plusargs_bit[arg] = some_arg_values[0].atoi();
	end else begin
	   results = {results, $psprintf("new-val:N/A \t\t //Not Overridden.") };
	end
	`uvm_info(where,$psprintf("%0s",results),verb)
     end
     INT : begin
        `uvm_info(where,$psprintf("INT: arg=%0s. val=%0d",arg,dflt),verb)
        plusargs_int[arg]=dflt;
	results = $psprintf("int plusarg name is: %0s. ",arg);
	if (uclp.get_arg_values(.match( {arg,"="} ), .values(some_arg_values))) begin
	   confirm_one_or_die(some_arg_values.size(), arg);
	   results = {results, $psprintf("new-val:%0d \t\t //Overridden.",some_arg_values[0].atoi()) };
           plusargs_int[arg] = some_arg_values[0].atoi();
	end else begin
	   results = {results, $psprintf("new-val:N/A  \t\t //Not Overridden.") };
	end
	`uvm_info(where,$psprintf("%0s",results),verb)
     end
     default : begin  //STRING
        `uvm_info(where,$psprintf("STRING: arg=%0s. val=%0s",arg,dflt_s),verb)
        plusargs_string[arg]=dflt_s;
	results = $psprintf("string plusarg name is: %0s. ",arg);
	if (uclp.get_arg_values(.match( {arg,"="} ), .values(some_arg_values))) begin
	   confirm_one_or_die(some_arg_values.size(), arg);
           plusargs_string[arg] = some_arg_values[0];
	   results = {results, $psprintf("new-val:%0s \t\t //Overridden.",some_arg_values[0]) };
	end else begin
	   results = {results, $psprintf("new-val:N/A  \t\t //Not Overridden.") };
	end
	`uvm_info(where,$psprintf("%0s",results),verb)
     end
   endcase
endfunction : add_plusarg


function void iclp::show_all_legal_plusarg_options(input string note="");
   string msg="Show all legal plusarg options";
   print_separator(msg,"Start");

   foreach (possible_args[i]) begin
      `uvm_info(where,$psprintf("%0s%0s:\t\t\/\/%0s",note,possible_args[i],possible_desc[i]), verb)
   end
   print_separator(msg,"End");
endfunction


function void iclp::show_all_received_plusargs(input string note="");
   string msg="Show all User-Supplied plusargs";
   print_separator(msg,"Start");

   foreach(all_arg_values[yy]) begin
      `uvm_info(where,$psprintf("User +arg: %0s",all_arg_values[yy]),verb)
   end
   print_separator(msg,"End");
endfunction

function void iclp::check_all_received_plusargs_are_legal();
   int verb = UVM_HIGH;
   string msg="Check legality of non-UVM plusargs";
   int plusarg_error=0;
   string arg_wo_val;  //plusarg with "=.*" (equal til end) stripped off

   print_separator(msg,"Start",UVM_HIGH);

   `uvm_info(where,$psprintf("arg #= %0d",all_arg_values.size()),verb)
   
   foreach(all_arg_values[zz]) begin
      `uvm_info(where,$psprintf("arg= %0s",all_arg_values[zz]),verb)

      arg_wo_val = remove_all_after_equal(all_arg_values[zz]);

      if (arg_wo_val.substr(0,3) == "+UVM") begin
         `uvm_info(where,$psprintf("+UVM arg     = %0s",arg_wo_val),verb)
      end else begin
	 if (!check_non_uvm_plusarg_is_legal(arg_wo_val)) begin
            plusarg_error++;
	 end
      end
   end

   if (plusarg_error) begin
      `uvm_fatal(where,$psprintf(" %0d bad plusarg(s) passed into sim. See earlier errors.",plusarg_error))
   end
   print_separator(msg,"End",verb);
endfunction : check_all_received_plusargs_are_legal

function bit iclp::check_non_uvm_plusarg_is_legal(input string arg);
   string where="check_non_uvm_plusarg_is_legal";
   int verb = UVM_HIGH;
   int results[$];
   bit pass;

   `uvm_info(where,$psprintf("non +UVM arg = %0s",arg),verb)
   results=possible_args.find_index with (item==arg);
   `uvm_info(where,$psprintf("non +UVM arg = %0s.  size=%0d",arg, results.size()),verb)
   if (results.size()==1) begin
      `uvm_info(where,$psprintf("Legal +arg: >>%0s<<",arg),verb)
      pass=1;
   end else begin
      `uvm_error(where,$psprintf("Illegal +arg: >>%0s<<  This was never defined.  !@#$",arg))
      pass=0;
   end

   return(pass);
endfunction : check_non_uvm_plusarg_is_legal


function void iclp::update_plusarg_values();
   string msg="Each Legal Plusargs - Update if Necessary.";
   string results="";
   print_separator(msg,"Start");
   $finish;
   //`uvm_info(where,$psprintf("loop thru all %0d possiblities",possible_args.size()),verb)
   foreach (plusargs_bit[aaa]) begin
      results = $psprintf("bit plusarg name is: %0s. ",aaa);
      if (uclp.get_arg_values(.match(aaa), .values(some_arg_values))) begin
	 confirm_one_or_die(some_arg_values.size(), aaa);
	 results = {results, $psprintf("new-val:%0d \t\t //Overridden.",some_arg_values[0].atoi()) };
	 plusargs_bit[aaa] = some_arg_values[0].atoi();
      end else begin
	 results = {results, $psprintf("new-val:N/A \t\t //Not Overridden.") };
      end
      `uvm_info(where,$psprintf("%0s",results),verb)
   end
   foreach (plusargs_int[bbb]) begin
      results = $psprintf("int plusarg name is: %0s. ",bbb);
      if (uclp.get_arg_values(.match( {bbb,"="} ), .values(some_arg_values))) begin
	 confirm_one_or_die(some_arg_values.size(), bbb);
	 results = {results, $psprintf("new-val:%0d \t\t //Overridden.",some_arg_values[0].atoi()) };
         plusargs_int[bbb] = some_arg_values[0].atoi();
      end else begin
	 results = {results, $psprintf("new-val:N/A  \t\t //Not Overridden.") };
      end
      `uvm_info(where,$psprintf("%0s",results),verb)
   end
   foreach (plusargs_string[ccc]) begin
      results = $psprintf("string plusarg name is: %0s. ",ccc);
      if (uclp.get_arg_values(.match( {ccc,"="} ), .values(some_arg_values))) begin
	 confirm_one_or_die(some_arg_values.size(), ccc);
         plusargs_string[ccc] = some_arg_values[0];
	 results = {results, $psprintf("new-val:%0s \t\t //Overridden.",some_arg_values[0]) };
      end else begin
	 results = {results, $psprintf("new-val:N/A  \t\t //Not Overridden.") };
      end
      `uvm_info(where,$psprintf("%0s",results),verb)
   end

   print_separator(msg,"End");
endfunction : update_plusarg_values


function int iclp::get_arg_values (string match, ref string values[$]);
   //   uclp.get_arg_values(match,values);

   //    `uvm_info(where,">>>-->>>");

   foreach (values[iii]) begin
      //`uvm_info(where,"GOT ARG: %0d: %0s +++++++", iii, values[iii]);
      if (values[iii]!=possible_args[0]) begin
         `uvm_info(where,$psprintf("BAD: %0d: %0s +++++++", iii, values[iii]),verb)
         $finish();
      end else begin
         `uvm_info(where,$psprintf("GOOD: %0d: %0s +++++++", iii, values[iii]),verb)
      end
   end
endfunction


function void iclp::show_all_final_values();
   string where="final_values";
   string name_val_overwritten_desc[4];
   
   //Step thru values in the same order they were defined in.
   //Indicate final value as well as if overwritten (and description).
 
   string msg="Show all final values";
   print_separator(msg,"Start");

   foreach (possible_args[mm]) begin
      name_val_overwritten_desc[0] = possible_args[mm];
      name_val_overwritten_desc[3] = possible_desc[mm];
      
   end

   print_separator(msg,"End");
endfunction : show_all_final_values


function void iclp::print_separator(input string string1, input string string2, input int my_verb=verb);
   //`uvm_info(where,$psprintf("************** %0s   %0s ***verb=%0d",string1,string2,verb),verb) //passing verb has issues
   `uvm_info(where,$psprintf("************** %0s   %0s ***",string1,string2),verb)
endfunction : print_separator

function void iclp::confirm_bool(input string name, input int val);
   if ( (val==0) || (val==1) ) begin
      `uvm_info(where,$psprintf("%0s is a bool, val=%0d",name,val),verb)
   end else begin
      `uvm_fatal(where,$psprintf("%0s should be bool, but is %0d",name,val))
   end
endfunction : confirm_bool

function void iclp::confirm_one_or_die(input int size, input string name);
   if (size!=1) begin
      `uvm_error(where,$psprintf("ERROR: %0s defined %0d times. Only 1x allowed. *** ERROR",name,size))
   end
endfunction : confirm_one_or_die

//Strip off possible "=" and all after it, to get bare plusarg
function string iclp::remove_all_after_equal(input string string1);
   string where="remove_all_after_equal";
   string que[$];
   uvm_split_string(string1,"=",que);
   foreach (que[pp]) begin
      `uvm_info(where,$psprintf("que[%0d] got:%0s",pp,que[pp]),verb)
   end
   return(que[0]);
endfunction : remove_all_after_equal


function int    iclp::add_plusarg_int(   input string name, input string desc, input int default_val);
   add_plusarg(.valtype(INT), .arg(name), .desc(desc), .dflt(default_val));
   return (i(name));
endfunction : add_plusarg_int

function string iclp::add_plusarg_string(input string name, input string desc, input string default_val);
   add_plusarg(.valtype(STRING), .arg(name), .desc(desc),   .dflt_s(default_val));
   return (s(name));
endfunction : add_plusarg_string

function bit    iclp::b(input string arg);
   string plusarg;
   plusarg = {"+",arg};
   return(plusargs_bit[plusarg]);
endfunction : b

function int    iclp::i(input string arg);
   string plusarg;
   //plusarg = {"+",arg};
   plusarg = {arg};
   return(plusargs_int[plusarg]);
endfunction : i

function string iclp::s(input string arg);
   string plusarg;
   //plusarg = {"+",arg};
   plusarg = {arg};
   return(plusargs_string[plusarg]);
endfunction : s