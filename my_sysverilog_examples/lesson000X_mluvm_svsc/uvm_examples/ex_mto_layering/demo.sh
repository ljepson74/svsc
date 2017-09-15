#! /bin/sh -f


command="-p @ex_mto_layering/demo";
quit_cmd=" "
test_name="ex_mto_layering/examples/ex_mto_layering_test"
run_mode=interactive
# =============================================================================
# Get args ( for the run_file)
#================================================================
usage() {
   echo "Usage: demo.sh"
}
# =============================================================================
while [ $# -gt 0 ]; do
   case `echo $1 | tr "[A-Z]" "[a-z]"` in
      -mode)
            run_mode=$2
            shift
            ;;
      -test_n)
	    test_name="$2"
            shift
            ;;
      -h|-help)
         usage
         exit 1
         ;;
	 -test)
	command="-p \"@$2 $3\""

	shift
	;;
      -run)
         quit_cmd="-c @$2"
	
         shift
    esac
    shift   
done
#================================================================
if [ $run_mode = batch ]; then
   command="-c \"load $test_name; test; exit\"";
   eval "specman $command"
   exit 0
fi
#================================================================

eval "specview $command $quit_cmd"

