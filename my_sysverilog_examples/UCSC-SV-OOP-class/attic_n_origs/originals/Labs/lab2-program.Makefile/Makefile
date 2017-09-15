# Makefile usage
#
help:
	@echo "==================================================";
	@echo "Usage:";
	@echo "  > make regress          - run all tests & generate summary";
	@echo "  > make summary          - generate summary";
	@echo "  > make test_index       - run individual test [see list below]";
	@echo "  > make clean            - run CLEAN script";
	@echo "";
	@echo "    Note: all test logfiles will be generated to ./logs/test_name.log";
	@echo "";
	@echo "    -----------------------------------------";
	@echo "    test_index      test_name";
	@echo "    -----------------------------------------";
	@echo "    t1              counter_sanity_check";
	@echo "    t2              counter_count2max";
	@echo "    t3              counter_count2max_bug";
	@echo "    t4              counter_disable_count";
	@echo "    t5              counter_reset_count";
	@echo "    t6              counter_reset_disable";
	@echo "    t7              counter_preload";
	@echo "    t8              counter_count2max_detect";
	@echo "==================================================";


# Makefile variables
#
VCS_CMD      = vcs -full64 +vcs+lic+wait -sverilog -R 
VCS_CMD_RAND = vcs -full64 +vcs+lic+wait -sverilog -R +ntb_random_seed_automatic

LOGS_DIR     = logs
VERILOG_DIR  = verilog

TESTBENCH    = ${VERILOG_DIR}/testbench.sv
COUNTER      = ${VERILOG_DIR}/counter.v
COUNTER_FIX  = ${VERILOG_DIR}/counter_fixed.v

# Makefile targets
#
regress: all_tests summary

all_tests: t1 t2 t3 t4 t5 t6 t7 t8

# Bogus targets -> map to real testnames
t1:counter_sanity_check
t2:counter_count2max
t3:counter_count2max_bug
t4:counter_disable_count
t5:counter_reset_count
t6:counter_reset_disable
t7:counter_preload
t8:counter_count2max_detect

counter_sanity_check:logdir
	${VCS_CMD} ${TESTBENCH} ${COUNTER} scenario/$@/testcase.sv -l ${LOGS_DIR}/$@.log

counter_count2max:logdir
	${VCS_CMD} ${TESTBENCH} ${COUNTER} scenario/$@/testcase.sv -l ${LOGS_DIR}/$@.log

counter_count2max_bug:logdir
	${VCS_CMD} ${TESTBENCH} ${COUNTER} scenario/$@/testcase.sv -l ${LOGS_DIR}/$@.log

counter_disable_count:logdir
	${VCS_CMD_RAND} ${TESTBENCH} ${COUNTER} scenario/$@/testcase.sv -l ${LOGS_DIR}/$@.log

counter_reset_count:logdir
	${VCS_CMD_RAND} ${TESTBENCH} ${COUNTER} scenario/$@/testcase.sv -l ${LOGS_DIR}/$@.log

counter_reset_disable:logdir
	${VCS_CMD_RAND} ${TESTBENCH} ${COUNTER} scenario/$@/testcase.sv -l ${LOGS_DIR}/$@.log

counter_preload:logdir
	${VCS_CMD_RAND} ${TESTBENCH} ${COUNTER} scenario/$@/testcase.sv -l ${LOGS_DIR}/$@.log

counter_count2max_detect:logdir
	${VCS_CMD_RAND} ${TESTBENCH} ${COUNTER_FIX} scenario/$@/testcase.sv -l ${LOGS_DIR}/$@.log

logdir:
	-mkdir ${LOGS_DIR}

summary:
	perl gen_summary.pl |tee summary.log

clean:
	rm -fr logs \
	summary.log \
	simv* \
	csrc \
	vcdplus.vpd \
	*DVE* \
	*INCA* \
	transcript \
	work \
	vc_hdrs.h \
        ucli.key
