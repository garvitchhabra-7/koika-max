// -*- mode: verilog -*-
// Generated by cuttlec from a Kôika module
module uart(input wire CLK, input wire RST_N, output wire write_bit_arg, input wire write_bit_out, output wire read_byte_arg, input wire[8:0] read_byte_out);
	reg[1:0] state = 2'b0;
	reg[7:0] data = 8'b0;
	reg[2:0] data_offset = 3'b0;
	reg last_write_ack = 1'b0;

	wire _cond0 = state == 2'b01;
	wire _cond1 = state == 2'b10;
	wire _cond2 = state == 2'b11;
	wire[1:0] _if_mux0 = _cond0 ? 2'b10 : (_cond1 ? (data_offset == 3'b111 ? 2'b11 : state) : (_cond2 ? 2'b0 : state));
	wire _0 = _if_mux0 == 2'b0;
	assign read_byte_arg = _0;
	wire _cond3 = _0 && read_byte_out[8 +: 1];
	assign write_bit_arg = _cond0 ? 1'b0 : (_cond1 ? data[3'b0] : ~_cond2);

	always @(posedge CLK) begin
		if (!RST_N) begin
			state <= 2'b0;
			data <= 8'b0;
			data_offset <= 3'b0;
			last_write_ack <= 1'b0;
		end else begin
			state <= _cond3 ? 2'b01 : _if_mux0;
			data <= _cond3 ? read_byte_out[0 +: 8] : (_cond0 || ~_cond1 ? data : data >> 1'b1);
			data_offset <= _cond0 || ~_cond1 ? data_offset : data_offset + 3'b001;
			last_write_ack <= write_bit_out;
		end
	end
endmodule
