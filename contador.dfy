class Celula
{
    var dados: int
    constructor ()
        ensures dados == 0

    {
        dados := 0;
    }


}


class Contador
{

    ghost var valor:int
    ghost var Repr:set<object>
    var incs:Celula
    var decs:Celula

    ghost predicate Valid()
        reads this, Repr
        ensures Valid() ==> this in Repr
    {

        this in Repr
        && incs in Repr
        && decs in Repr
        && incs.dados >= 0
        && decs.dados >= 0
        && valor == incs.dados - decs.dados

    }

    constructor ()
        ensures valor == 0
        ensures Valid()
    {

        incs := new Celula();
        decs := new Celula();
        valor := 0;
        Repr := {this, incs, decs};

    }

    method Incrementar()
        requires Valid()
        modifies Repr
        ensures valor == old(valor) + 1
        ensures fresh(Repr - old(Repr))
        ensures Valid()
    {
        incs.dados := incs.dados + 1;
        valor := valor + 1; 

    }
    
    method Decrementar()
        requires Valid()
        modifies Repr
        ensures valor == old(valor) - 1
        ensures fresh(Repr - old(Repr))
        ensures Valid()
    {
        decs.dados := decs.dados + 1;
        valor := valor - 1; 

    }

    function GetValor():int
        reads Repr
        requires Valid()
        ensures GetValor() == valor
    


}


method main()
{
    var c := new Contador();
    c.Incrementar();
    c.Incrementar();
    c.Decrementar();

    assert c.GetValor() == 1;
}