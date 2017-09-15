#!/bin/csh -f

set irunCmplString = "\*E"
set irunCompileCheckFile = ".irun_check"


# do grid commands
set command1 = "do.grid -jobname preIrun -vmem 2000 -kew ALPHA:FARM:BETA:YARD -do irun -c -licqueue $*"
set command2 = "do.grid -jobname Irun_72 -vmem 2000 -kew ALPHA:FARM:BETA:YARD --l Incisive_HDL_Simulator__AND__VERILOG-XL -do irun -licqueue $*"

# Check domain
set domainCheckFile = ".domain_check"
uname -a | grep caustic.com | grep -v frozone  >! ${domainCheckFile}

if (! -z ${domainCheckFile}) then 
    #
    echo "No grid.  Just use irun"
    setenv NETHRA /opt/arm/tsmc90g/
    setenv ARM    /opt/arm/tsmc90g/
    setenv PARSEC ../..

## CT 24-Feb-2011 Add IMGUSER
    if (! $?IMGUSER) then
      echo "CAUSTIC_ERROR: Must set IMGUSER environment variable to run off-grid"
      exit (1)
    endif

    # simple irun command
    set causticCmd0 = "/usr/bin/rsh -l ${IMGUSER} sun1.seg GetLic Incisive_Enterprise_Simulator__AND__VERILOG-XL "
    set causticCmd1 = "irun -licqueue $*"

    ${causticCmd0}    # get license
    ${causticCmd1}    # actual irun call
else 
    #
    echo "Domain with grid.  Let's use it."
    setenv NETHRA /projects/caustic/ip/trunk/nethra/tsmc90g/
    setenv ARM    /projects/caustic/ip/trunk/arm/tsmc90g/
    setenv PARSEC ../..
    
    echo ""
    echo "use do.grid to precompile and elaborate the design but without starting simulation (irun -c)"
    echo "starting: ${command1}"
    echo "----------------------------------------------"
    ${command1}
    echo "----------------------------------------------"
    echo "completed: ${command1}"
    echo ""

    echo "Checking irun compilation status."
    egrep "$irunCmplString" irun.log* >! ${irunCompileCheckFile}

    if (! -z ${irunCompileCheckFile}) then 
	echo ""
	echo "irun compilation failed.  See irun.log* for messages."
	echo ""
    else
	echo ""
	echo "use do.grid to run the simulation (irun)"
	echo "starting: ${command2}"
	echo "----------------------------------------------"
	${command2}
	echo "----------------------------------------------"
	echo "completed: ${command2}"
	echo ""
    endif
	
    # clean up irun compile check file
    rm ${irunCompileCheckFile}
endif

# clean up domain check file
rm ${domainCheckFile}
