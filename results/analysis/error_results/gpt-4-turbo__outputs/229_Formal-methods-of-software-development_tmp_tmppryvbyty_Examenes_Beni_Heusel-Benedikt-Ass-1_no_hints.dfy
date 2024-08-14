
// APELLIDOS: Heusel
// NOMBRE: Benedikt
// ESPECIALIDAD: ninguna (Erasmus)

// ESTÁ PERFECTO, NO HAY NINGUN COMENTARIO MAS ABAJO

// EJERCICIO 1 
// Demostrar el lemma div10_Lemma por inducción en n 
// y luego usarlo para demostrar el lemma div10Forall_Lemma

function exp(x: int, e: nat): int
{
    if e == 0 then 1 else x * exp(x, e-1)
}

lemma div10_Lemma(n: nat)
    requires n >= 3;
    ensures (exp(3, 4*n) + 9) % 10 == 0
{
    if n == 3 {
        calc {
            (exp(3, 4*n) + 9);
            (exp(3, 4*3) + 9);
            exp(3, 12) + 9;
            531441 + 9;
            531450;
            531450 % 10;
            0;
        }
    } else {
        div10_Lemma(n-1);
        assert (exp(3, 4*(n-1)) + 9) % 10 == 0;
        calc {
            exp(3, 4*n) + 9;
            3 * 3 * exp(3, 4*n - 2) + 9;
            3 * 3 * 3 * 3 * exp(3, 4*n - 4) + 9;
            81 * exp(3, 4*n - 4) + 9;
            81 * (exp(3, 4*(n-1)) + 9) / 10 * 10;
            81 * 10 * ((exp(3, 4*(n-1)) + 9) / 10);
            810 * ((exp(3, 4*(n-1)) + 9) / 10);
            10 * (81 * ((exp(3, 4*(n-1)) + 9) / 10));
            0;
        }
    }
}

lemma div10Forall_Lemma()
    ensures forall n :: n >= 3 ==> (exp(3, 4*n) + 9) % 10 == 0
{
    forall n | n >= 3 {
        div10_Lemma(n);
    }
}

// EJERCICIO 2
// Demostrar por inducción en n el lemma de abajo acerca de la función sumSerie que se define primero.

function sumSerie(x: int, n: nat): int
{
    if n == 0 then 1 else sumSerie(x, n-1) + exp(x, n)
}

lemma sumSerie_Lemma(x: int, n: nat)
    ensures (1-x) * sumSerie(x, n) == 1 - exp(x, n+1)
{
    if n == 0 {
        calc {
            (1-x) * sumSerie(x, n);
            (1-x) * sumSerie(x, 0);
            (1-x) * 1;
            1 - x;
            1 - exp(x, 1);
            1 - exp(x, n+1);
        }
    } else {
        sumSerie_Lemma(x, n-1);
        assert (1-x) * sumSerie(x, n-1) == 1 - exp(x, n);
        calc {
            (1-x) * sumSerie(x, n);
            (1-x) * (sumSerie(x, n-1) + exp(x, n));
            (1-x) * sumSerie(x, n-1) + (1-x) * exp(x, n);
            1 - exp(x, n) + (1-x) * exp(x, n);
            1 - exp(x, n) + exp(x, n) - x * exp(x, n);
            1 - x * exp(x, n);
            1 - exp(x, n+1);
        }
    }
}
