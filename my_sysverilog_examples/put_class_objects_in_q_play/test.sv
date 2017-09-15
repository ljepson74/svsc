//Objective: figure out how to pass objects (class instances) through a queue; either directly or using handles.

program test;

   class_abc myq[$];
   int result;


   class_abc my_object2;

   task q_put(class_abc handleX);      
      $display("%0d %0d :inputX",handleX.n1,handleX.n2);        
      myq.push_back(handleX);
      //     my_object2 = myq.pop_front();
      //   $display("result_a=%0d result_b=%0d",my_object2.n1,my_object2.n2);
   endtask

   task q_get();
      class_abc handleY;

      for (int j=0; j<10; j++)
	begin
	   handleY = myq.pop_back();
	   $display("%0d %0d : outputY",handleY.n1,handleY.n2); 
	end
   endtask


   class_abc handle1;
   initial
     begin
	$display(" ***** START TEST *****");

	for (int i=0; i<10; i++)
	  begin
	     handle1     = new();
	     assert ((handle1.randomize() with {n1>0; n1<10; n2>0; n2<10;}) ==1) else begin $error(" * * * Randomization failed * * * "); end
	     //	my_object.n1  = 5; //my_object.n2  = 555;
	     //$display("%0d %0d :in",handle1.n1, handle1.n2);
	     q_put(handle1);
	     end // for (int i		      =0; i<10; i++)

	q_get();	
     end

endprogram // test
