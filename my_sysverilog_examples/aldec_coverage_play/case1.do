transcript file coverage_play.aldec_log

vlib work
vdel -lib work -all

set worklib work

#set PARSEC ../..

alog ./coverage_play.sv

vsim -lib work case1

fcover report -db fcover.acdb -file fcover_report_case1.txt

run

quit


