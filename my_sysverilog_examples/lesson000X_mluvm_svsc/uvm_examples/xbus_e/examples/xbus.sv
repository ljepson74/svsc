
# SimVision Command Script 
#
# Design Browser windows
#
if {[window find -match exact -name "Design Browser 1"] == {}} {
    window new WatchList -name "Design Browser 1" -geometry 1042x500+9+224
} else {
    window geometry "Design Browser 1" 1042x500+9+224
}
window target "Design Browser 1" on
browser using {Design Browser 1}
browser timecontrol set -lock 0
#
# Waveform windows
#
if {[window find -match exact -name "Waveform 1"] == {}} {
    window new WaveWindow -name "Waveform 1" -geometry 1010x600+128+172
} else {
    window geometry "Waveform 1" 1010x600+128+172
}
window target "Waveform 1" on
waveform using {Waveform 1}
waveform sidebar select designbrowser
waveform set \
    -primarycursor TimeA \
    -signalnames name \
    -signalwidth 175 \
    -units ns \
    -valuewidth 75
cursor set -using TimeA -time 0
cursor set -using TimeA -marching 1
waveform baseline set -time 0

set id [waveform add -signals simulator::xbus_evc_demo.xbus_req_master_0]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}
set id [waveform add -signals simulator::xbus_evc_demo.xbus_gnt_master_0]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}
set id [waveform add -signals simulator::xbus_evc_demo.xbus_req_master_1]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}
set id [waveform add -signals simulator::xbus_evc_demo.xbus_gnt_master_1]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}
set id [waveform add -signals simulator::xbus_evc_demo.xbus_clock]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}
set id [waveform add -signals simulator::xbus_evc_demo.xbus_reset]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}
set id [waveform add -signals simulator::xbus_evc_demo.xbus_addr]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}
set id [waveform add -signals simulator::xbus_evc_demo.xbus_size]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}
set id [waveform add -signals simulator::xbus_evc_demo.xbus_read]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}
set id [waveform add -signals simulator::xbus_evc_demo.xbus_write]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}
set id [waveform add -signals simulator::xbus_evc_demo.xbus_start]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}
set id [waveform add -signals simulator::xbus_evc_demo.xbus_bip]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}
set id [waveform add -signals simulator::xbus_evc_demo.xbus_data]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}
set id [waveform add -signals simulator::xbus_evc_demo.xbus_wait]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}
set id [waveform add -signals simulator::xbus_evc_demo.xbus_error]
waveform format $id -radix %b -trace digital -color #00ff00 -symbol {}


waveform xview limits 0 2000ns

