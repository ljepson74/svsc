#!/bin/csh -f
########################################################################
# Filename    : setup.csh
# Author      : Cadence Design Systems
# Date        : January 2011
# Description : Environment configuration script
#               This script is divided into 2 main sections. The 
#               USER CONFIGURABLE VARIABLES section contains variables
#               that should be defined by the user. The 
#               AUTOMATIC VARIABLE CONFIGURATION section contains 
#               variables that should be set automatically. These
#               variables should not be changed by the user.  
########################################################################
########################################################################
# USER CONFIGURABLE VARIABLES
#
# The user is responsible for defining the variables in this section
########################################################################

# Emulator type
# Set this variable to : PD for Palladium systems
#                      : PDXP for PalladiumXP systems

set EMTYPE = PDXP


# Path to uvm_accel package
setenv UVM_ACCEL  `sn_which.sh uvm_accel-1.0`

# Path to IES software installation
setenv IESHOME ${CDS_TOOLS}/ius/9.2/latest

# Path to Specman installation
setenv VRST_HOME ${CDS_TOOLS}/spmn/9.2/latest

# Path to IXE software installation
setenv IXEHOME ${CDS_TOOLS}/ixe/5.2.1/latest

# Path to UXE software installation
setenv UXEHOME  ${CDS_TOOLS}/uxe/10.2/latest



# Set this variable to : 32 for 32-bit software
#                      : 64 for 64-bit software
setenv BITMODE 32

# Emulator host name
setenv EMHOST "fetlar"
#setenv EMHOST "cva-faelab5"

# Emulator domains
setenv EMDOMAINS "0.8"
#setenv EMDOMAINS "0.0"

# Configure licenses
setenv CDS_LIC_FILE 5280@cdsuk1:83817@cdsuk1

########################################################################
# END OF USER CONFIGURABLE VARIABLES
########################################################################

########################################################################
# AUTOMATIC VARIABLE CONFIGURATION
#
# The user should not need to modify any variables below this point
########################################################################

# More license file configuration
setenv LM_LICENSE_FILE ${CDS_LIC_FILE}

# Emulator Configuration
setenv EMCONFIG "host ${EMHOST} boards ${EMDOMAINS}"

# Configure Platform
setenv PLATFORM `${IXEHOME}/bin/qt_virtual_platform ${BITMODE}`

# Set AXIS_HOME
setenv AXIS_HOME ${UXEHOME}/tools.lnx86

# Set QTHOME
if ("${EMTYPE}" == "PDXP") then
  setenv QTHOME ${AXIS_HOME}
else
  setenv QTHOME ${IXEHOME}
endif

# Set Specman environment
if ( ${?VRST_HOME} ) then
  if (${BITMODE} == 64) then
    source $VRST_HOME/env.csh -64bit
  else
    source $VRST_HOME/env.csh
  endif
endif

# Configure BIT Mode
if (${BITMODE} == "64") then
  setenv GCC_BIT "64Bit"
  setenv AXIS_BIT "64bit"
else
  setenv GCC_BIT
  setenv AXIS_BIT "32bit"
endif

# Configure Path
set COPY_PATH = ${PATH}
unsetenv PATH
if ("${EMTYPE}" == "PDXP") then
  setenv PATH ${UXEHOME}/bin:${IESHOME}/tools/bin/:${IESHOME}/tools/inca/bin/:${IESHOME}/tools/systemc/gcc/bin/${GCC_BIT}:${COPY_PATH}
else
  setenv PATH ${IESHOME}/tools/bin/:${IESHOME}/tools/inca/bin/:${IESHOME}/tools/systemc/gcc/bin/${GCC_BIT}:${IXEHOME}/bin:${COPY_PATH}
endif

# Configure LD_LIBRARY_PATH
if ( ! $?LD_LIBRARY_PATH ) then
  setenv LD_LIBRARY_PATH
endif

set COPY_LD_LIBRARY_PATH = ${LD_LIBRARY_PATH}
unsetenv LD_LIBRARY_PATH
if ("${EMTYPE}" == "PDXP") then
  setenv LD_LIBRARY_PATH ${AXIS_HOME}/lib/${AXIS_BIT}:${IESHOME}/tools/lib/:${IESHOME}/tools/inca/lib/:${IESHOME}/tools/systemc/lib/gnu:${IESHOME}/tools/tbsc/lib/gnu:${IESHOME}/tools/systemc/gcc/install/lib:${COPY_LD_LIBRARY_PATH}
else
  setenv LD_LIBRARY_PATH ${IESHOME}/tools/lib/:${IESHOME}/tools/inca/lib/:${IESHOME}/tools/systemc/lib/gnu:${IESHOME}/tools/tbsc/lib/gnu:${IESHOME}/tools/systemc/gcc/install/lib:${IXEHOME}/lib/${PLATFORM}:${COPY_LD_LIBRARY_PATH}
endif

# Configure SPECMAN_PATH
if ( ! $?SPECMAN_PATH ) then
  setenv SPECMAN_PATH
endif

set COPY_SPECMAN_PATH = ${SPECMAN_PATH}
unsetenv SPECMAN_PATH
setenv SPECMAN_PATH ${COPY_SPECMAN_PATH}:${UVM_ACCEL}/../

echo " "
echo "Configuring Environment"
echo " - IESHOME       : ${IESHOME}";
if  ("${EMTYPE}" == "PD") then
  echo " - IXEHOME       : ${IXEHOME}";
else if ("${EMTYPE}" == "PDXP") then
  echo " - UXEHOME       : ${UXEHOME}";
else
   echo " - EMULATOR HOST UNKNOWN";
endif
if ( ${?VRST_HOME} ) then
  echo " - VRST_HOME     : ${VRST_HOME}";
endif
echo " - PLATFORM      : ${PLATFORM}";
echo " - BITMODE       : ${BITMODE}";
echo " - EMULATOR      : ${EMCONFIG}";
echo " - EMULATOR TYPE : ${EMTYPE}";
echo "Done"
echo " "

