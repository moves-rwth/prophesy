//example TACAS submission

dtmc

module test
v1 : [0..1];
v2 : [0..1];
v3 : [0..1];
v4 : [0..1];

[] v1=0 & v2=0 & v3=0 -> 0.5: (v3'=1) + 0.25: (v2'=1) + 0.25: (v1'=1) & (v2' = 1);
[] v1=0 & v2=0 & v3=1 -> 0.5: (v2'=1) & (v3'=0) + 0.5: (v2'=1);
[] v1=0 & v2=1 & v3=0 -> 0.5: (v2'=0) & (v3'=1) + 0.5: (v1'=1) & (v2'=1) & (v3'=1);
[] v1=0 & v2=1 & v3=1 -> 1: (v1'=0) & (v2'=1) & (v3'=1);
[] v1=1 & v2=1 & v3=1 -> 0.7: (v1'=0) & (v2'=0) + 0.3: (v1'=0);
[] v1=1 & v2=1 & v3=0 -> 1: (v2'=0);
[] v1=1 & v2=0 & v3=0 -> 0.5: (v1'=0) & (v2'=1) & (v3'=1) + 0.5: (v3'=1);
[] v1=1 & v2=0 & v3=1 -> 0.25: (v2'=1) & (v3'=0) + 0.25: (v3'=0) + 0.5: (v4'=1);

endmodule

// labels
label "target" = v1=0&v2=1&v3=1&v4=0;
