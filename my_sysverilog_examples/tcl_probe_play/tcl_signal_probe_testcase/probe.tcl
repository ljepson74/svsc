
set TOP test_drink.drink_machine_top


database -open evcd_file_for_you -evcd -default
probe -create -evcd $TOP -all \
 -exclude $TOP.clk          \
 -exclude $TOP.sd1_rd_en_io

run
exit


# notes
##database -open testoutput -evcd
#p robe -create test_drink.top -evcd -outputs
#probe -create test_drink.top -evcd -exclude test_drink.reset
#probe -create -evcd test_drink.top -all -exclude test_drink.top.reset

#works
#probe -create -evcd test_drink.drink_machine_top -all \
# -exclude test_drink.drink_machine_top.reset          \
# -exclude test_drink.drink_machine_top.nickel_out
