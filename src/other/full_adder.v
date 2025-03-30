module full_adder (
    input A, B, Cin,
    output Sum, Cout
);
    wire AxorB, AB, CinAxorB;
    
    xor (AxorB, A, B);
    xor (Sum, AxorB, Cin);
    and (AB, A, B);
    and (CinAxorB, Cin, AxorB);
    or (Cout, AB, CinAxorB);
endmodule
