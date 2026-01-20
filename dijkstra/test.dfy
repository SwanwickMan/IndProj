method triple(x: int) returns (r:int){
        if {
            case x < 18 =>
                r := x * 3;
            case x >= 0 =>
                r := x * -3;
        }
        assert true;

   }

method Main(){
    var a := triple(10);
    print "output ";
    print a;
}