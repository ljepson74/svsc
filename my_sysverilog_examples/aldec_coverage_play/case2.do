transcript file coverage_play.aldec_log

vlib work
vdel -lib work -all

set worklib work

#set PARSEC ../..

alog ./coverage_play.sv

vsim -lib work case2

fcover report -db fcover.acdb -file fcover_report_case2.txt

run

quit



