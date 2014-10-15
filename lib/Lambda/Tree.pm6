use v6;

my $ctorCalls = 0;

role Tree {

    method children { !!! }

    method BUILDALL(|args) {
        $ctorCalls++;
        callsame;
    }

    method ctorCalls {
        $ctorCalls;
    }

    method childCount {
        self.children.map(*.size).reduce(* + *)
    }
    
    method size {
        1 + self.childCount
    }

    method Str { self.gist }

}


role Leaf does Tree {
    method children { @() }
}
