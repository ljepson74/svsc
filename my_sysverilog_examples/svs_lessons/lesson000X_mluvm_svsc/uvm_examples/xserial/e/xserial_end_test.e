/*------------------------------------------------------------------------- 
File name   : xserial_end_test.e
Title       : End of test stuff
Project     : XSerial eVC
Created     : 2008
Description : This file handles 'end of test'.
Notes       : End of test handling is done using the objection mechanism.
            : Each proactive MAIN sequence raises an objection to TEST_DONE
            : at the start of the sequence and drops the objection at the
            : end of the sequence. A built in drain time is used to ensure 
            : that the test has really finished.
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide

-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;


extend MAIN xserial_sequence {
    prevent_test_done : bool;
       keep soft prevent_test_done == TRUE;
}; -- extend xserial_sequence 

extend MAIN ENV_SETUP xserial_sequence {
    -- Raise an objection to TEST_DONE at setup
    pre_body() @sys.any is first {
        message(TESTFLOW_EX, LOW, "MAIN ENV_SETUP sequence started");
        if prevent_test_done {
            driver.raise_objection(TEST_DONE);
        };
    }; -- pre_body()
};

extend MAIN POST_TEST xserial_sequence {
    -- This field is used to control the delay between the end of the MAIN
    -- sequence and the dropping of the objection to TEST_DONE - i.e. the
    -- time allowed for the last data to drain through the DUT. This is
    -- measured in clock cycles. 
    drain_time : uint;
        keep soft drain_time == 10;
};


extend MAIN POST_TEST xserial_sequence {
    -- Drop the objection to TEST_DONE after the MAIN sequence ends &
    -- waited defined drain_time
    post_body() @sys.any is also {
        message(TESTFLOW_EX, LOW, "MAIN POST_TEST sequence finished");
        if prevent_test_done {
            wait [drain_time] * cycle @driver.clock;
            driver.drop_objection(TEST_DONE);
        };
    }; -- post_body()
    
}; -- extend MAIN xserial_sequence



'>
