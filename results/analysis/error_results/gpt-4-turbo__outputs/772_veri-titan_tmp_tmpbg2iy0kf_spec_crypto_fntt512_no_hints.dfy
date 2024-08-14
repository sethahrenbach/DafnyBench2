
// Assuming the necessary imports and types are correctly defined and accessible.

module ntt_impl {
    import opened ct_std2rev_model

    method j_loop(a: seq<int>, p: seq<int>, t: nat, d: nat, j: nat, u: nat, ghost view: ct_std2rev_model.loop_view)
    returns (a': seq<int>)
        requires u == j * (2 * d)
        requires view.j_loop_inv(a, d, j)
        requires t == view.lsize()
        requires p == ct_std2rev_model.rev_mixed_powers_mont_table()
        requires j < view.lsize()
        ensures view.j_loop_inv(a', d, j + 1)
    {
        view.s_loop_inv_pre_lemma(a, d, j);
        var w := p[t + j];
        var s := u;
        a' := a;
        while s < u + d
            invariant view.s_loop_inv(a', d, j, s-u)
        {
            var e := a[s];
            var o := a[s + d];
            var x := ct_std2rev_model.montmul(o, w);
            a' := a[s+d := ct_std2rev_model.mqsub(e, x)];
            a' := a'[s := ct_std2rev_model.mqadd(e, x)];
            s := s + 1;
            view.s_loop_inv_peri_lemma(a, a', d, j, s-u);
        }
        view.s_loop_inv_post_lemma(a', d, j, d);
    }
}
