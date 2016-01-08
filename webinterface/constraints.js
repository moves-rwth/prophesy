function sign(x) {
    if(x > 0) {
        return 1;
    } 
    if (x < 0) {
        return -1;
    }
    return 0;
}

/*
 * @param A 2-dimensional point
 * @param B 2-dimensional point
 * @param C 2-dimensional point
 * 
 * Reports on which side of a line from A to B the point C lies.
 */
function sideOfLine(A, B, C) {
    return sign((B[0]-A[0])*(C[1]-A[1]) - (B[1]-A[1])*(C[0]-A[0]));
}

