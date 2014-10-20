use v6;

use Test;
use Lambda::Base;

plan 8;

{
    is $id("x"), "x", 'id("x")';
    is $id(5), 5, 'id(5)';
    is $id($id), $id, 'id(id)';
}

{
    is $const("x")(5), "x", 'const("x")(5)';
    is $const(5)(23), 5, 'const(5)(23)';
    is $const(42).Str, "λy.42", 'const(42).Str';
    is $const($id)(23), $id, 'const(id)(23)';
    is $const($id).Str, 'λy.' ~ $id.Str, 'const($id).Str';
}

{
    #is $const("x", 5), "x", 'const("x", 5)';
    #is $const(5, 23), 5, 'const(5, 23)';
    #is $const($id, 23), $id, 'const(id, 23)';
}
