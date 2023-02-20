dtmc

const double p;
const double q;

module now
    s : [0..2] init 0;
    [] s=0 -> p+q: (s'=1) +  1-p-q: (s'=2);
    [] s>0 -> (s'=s);
endmodule