#!nqp

use testing;
use Util;
use Util::QAST;

use Util::Compiler;

plan(4);

{ # - panic -------------------------------------------------------------------
    ok(nqp::isinvokable(&panic), 'sub panic is there');
    dies_ok({ panic(NQPMu, 'a', 5)}, 'panic without a match and some msg pieces');
}

{ # - match2location ----------------------------------------------------------
    ok(nqp::isinvokable(&match2location), 'sub match2location is there');
}

{ # - loc2str -----------------------------------------------------------------
    ok(nqp::isinvokable(&loc2str), 'sub loc2str is there');
}

done();
