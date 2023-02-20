mdp

const double p;
const double q;

module mini
    s : [0..2] init 0;
    [] s = 0 -> p: (s'=1) + 1-p: (s'=2);
    [] s = 0 -> q: (s'=1) + 1-q: (s'=2);
    [] s > 0 -> 1: (s'=s);
endmodule
