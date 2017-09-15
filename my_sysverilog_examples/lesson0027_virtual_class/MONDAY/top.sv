module top;

   initial begin
      kl_class h_kl_class;
      sv_class h_sv_class;
      h_kl_class = new();
      h_sv_class = new();

      h_kl_class = h_sv_class;
//    h_sv_class = h_kl_class;

      h_sv_class.whoami();
      h_kl_class.whoami();
   end
endmodule