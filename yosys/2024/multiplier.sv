// Designed by Michalis Pardalos
// Modified by John Wickerson

module multiplier (
		   input 	 rst,
                   input 	 clk,
                   input [7:0] 	 in1,
                   input [7:0] 	 in2,
                   output [15:0] out
                  );
   reg [3:0]  stage = 0;
   reg [15:0] accumulator = 0;
   reg [7:0]  in1_shifted = 0;
   reg [15:0] in2_shifted = 0;


   // Logic for controlling the stage
   always @(posedge clk) 
     if (rst || stage == 9)
       stage <= 0;
     else
       stage <= stage + 1;
   
   // Logic for in1_shifted and in2_shifted
   always @(posedge clk) 
     if (rst) begin
	in1_shifted <= 0;
	in2_shifted <= 0;
     end else if (stage == 0) begin
        in1_shifted <= in1;
        in2_shifted <= in2;
     end else begin
        in1_shifted <= in1_shifted >> 1;
        in2_shifted <= in2_shifted << 1;
     end

   // Logic for the accumulator
   always @(posedge clk)
     if (rst || stage == 9) begin
	accumulator <= 0;
     end else if (in1_shifted[0]) begin
        accumulator <= accumulator + in2_shifted;
     end

   // Output logic
   assign out = accumulator;


`ifdef FORMAL
  reg [7:0] in1_past = 0;
  reg [15:0] in2_past = 0;
  always @(posedge clk) begin
    if(stage == 0)
    begin
      in1_past <= in1;
      in2_past <= in2;
    end
    else
    begin
      in1_past <= in1_past;
      in2_past <= in2_past;
    end
  end
  always_comb begin
    if(in1_past != 1 && in2_past != 1)begin
      cover(accumulator == 13 && stage ==9);
    end
  end

   always @(posedge clk) begin

    // task 1:
    assert(out <= 'hfe02);
    // task 2:
    if (stage != 0) begin
        assert(stage == $past(stage) + 1);
        //task4:
        assert(out >= $past(out));
        //task7:
        assert(in1_shifted == in1_past >> $past(stage));
        //task8:
        assert(in2_shifted == in2_past << $past(stage));
    end 
    //task5:
    if (stage == 5) begin 
        assert(accumulator == $past(in2,5) * $past(in1[3:0],5));
    end
    //task6:
    if (stage == 2) begin 
        assert(accumulator == $past(in2,2) * $past(in1[0:0],2));
    end
    if (stage == 3) begin 
        assert(accumulator == $past(in2,3) * $past(in1[1:0],3));
    end
    if (stage == 4) begin 
        assert(accumulator == $past(in2,4) * $past(in1[2:0],4));
    end
    if (stage == 6) begin 
        assert(accumulator == $past(in2,6) * $past(in1[4:0],6));
    end
    if (stage == 7) begin 
        assert(accumulator == $past(in2,7) * $past(in1[5:0],7));
    end
    if (stage == 8) begin 
        assert(accumulator == $past(in2,8) * $past(in1[6:0],8));
    end
    //task3:
    if (stage == 9) begin 
        assert(accumulator == $past(in2,9) * $past(in1[7:0],9));
    end

   end

`endif
   
   
endmodule
