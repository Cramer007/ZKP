use ark_bls12_381::{Fr as ScalarField, G1Projective as Gr};
use ark_ff::{Field, PrimeField};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
use ark_std::{ops::{Mul}, UniformRand};
use ark_std::rand::Rng;

fn hash(s: &str) -> ScalarField {
    //Fonction de hashage qui prend une chaine de caractère et renvoie un élément du groupe
    return ScalarField::from_le_bytes_mod_order(s.as_bytes());
}

fn keygen<R: Rng>(rng: &mut R, g: Gr, n: usize) -> (Vec<ScalarField>, Vec<Gr>) {
    //Fonction qui prend un n et renvoie n clee privee Si et n clee public Vi = Si*G

    let mut sis = Vec::new();
    let mut vis = Vec::new();

    //Creation de n clee privee et public
    for _ in 0..n {
        let si = ScalarField::rand(rng);
        let vi = g.mul(si);
        sis.push(si);
        vis.push(vi);
    }

    (sis, vis)
}

fn f(a: Vec<ScalarField>, t: Vec<ScalarField>, vis: Vec<Gr>, g: Gr) -> Vec<Gr> {
    //Fonction qui sert au prouveur de montrer qu'il posède un antécédent de (V1, ...., Vn) par f(wa, wt)


    //Creation du Polynome p(x) =0 + a_1*x + ... + a_n-1*x^n-1
    //On prend 0 pour le premier coefficient pour ne pas avoir à retirer Vi par la suite
    let mut coeffs = Vec::new();
    coeffs.push(ScalarField::from(0));
    for i in 0..a.len() {
        coeffs.push(a[i]);
    }
    let p = DensePolynomial::from_coefficients_slice(&coeffs);

    //Calcule des (P(i)V(i) - t(i)G))
    let mut res = Vec::new();
    for i in 0..t.len() {
        res.push(g.mul(t[i]) - vis[i].mul(p.evaluate(&ScalarField::from((i + 1) as i32))));
    }

    res
}

fn prover(m: &str, g: Gr, vis: Vec<Gr>, si: ScalarField, n: usize, indice_prouveur: usize) -> (ScalarField, Vec<ScalarField>, Vec<ScalarField>){
    //prover effectue une preuve de connaissance de Vis=f(wa,wt), tout les vecteurs sont divisés en parties relatives à a_1,..a_n-1 et t_1,..t_n
    


    //Creation du polynome p(x) = (1-x)(2-x)...(n-x) * i / (n! (i-x))
    //Il vaux 0 pour tout x de 1 à n sauf pour x = i
    //P(0) = 1
    let mut p = DensePolynomial::from_coefficients_slice(&(vec![ScalarField::from(if n % 2 == 0 { -1 } else { 1 })]));

    for j in 1..n + 1 {
        if j != indice_prouveur {
            let mut coeffs = Vec::new();
            coeffs.push(ScalarField::from(-1));
            let j_scalar = ScalarField::from(j as i32);
            let j_inv = j_scalar.inverse().unwrap();
            coeffs.push(j_inv);
            let pj = DensePolynomial::from_coefficients_slice(&coeffs);
            p = p.mul(&pj);
        }
    }

    //Calcule de W (wa, wt)
    let ti =  p.evaluate(&ScalarField::from(indice_prouveur as i32)) * si;
    let coeffs = p.coeffs();
    let mut wa = Vec::new();
    for i in 1..n {
        wa.push(coeffs[i]);
    }
    let mut wt = Vec::new();
    for _ in 1..indice_prouveur {
        wt.push(ScalarField::from(0));
    }
    wt.push(ti);
    for _ in indice_prouveur + 1..n + 1 {
        wt.push(ScalarField::from(0));
    }


    //Calcul d'un element aléatoire
    let mut ra = Vec::new();
    let mut rt = Vec::new();
    for _ in 0..n-1{
        ra.push(ScalarField::rand(&mut ark_std::test_rng()));
        rt.push(ScalarField::rand(&mut ark_std::test_rng()));
    }
    rt.push(ScalarField::rand(&mut ark_std::test_rng()));
    
    //Calcul de f(r)
    let a = f(ra.clone(), rt.clone(), vis.clone(), g);

    //Calcul de H(vis, a, m)
    let mut total_str = "".to_string();
    for i in 0..vis.len() {
        total_str = total_str + &vis[i].to_string();
    }
    for i in 0..a.len() {
        total_str = total_str + &a[i].to_string();
    }

    let e = hash(&(total_str + m));
    
    //Calcule de e*w
    let mut e_wa: Vec<ScalarField> = Vec::new();
    let mut e_wt: Vec<ScalarField> = Vec::new();
    for i in 0..n-1 {
        e_wa.push(e * wa[i]);
        e_wt.push(e * wt[i]);
    }
    e_wt.push(e * wt[n-1]);

    //Calcul de z = r + e*w
    let mut za: Vec<ScalarField> = Vec::new();
    let mut zt: Vec<ScalarField> = Vec::new();
    for i in 0..n-1 {
        za.push(ra[i] + e_wa[i]);
        zt.push(rt[i] + e_wt[i]);
    }
    zt.push(rt[n-1] + e_wt[n-1]);

    (e, za, zt)
}


fn verifier(m: &str, g: Gr, vis: Vec<Gr>, n: usize, proof_e: ScalarField, za: Vec<ScalarField>, zt: Vec<ScalarField>) -> bool{
    //Verifier vérifie la preuve de connaissance de e = H(x, (f(z) - e*x), m)

    //Calcul de e*vis
    let mut e_vis: Vec<Gr> = Vec::new();
    for i in 0..n {
        e_vis.push(vis[i].mul(proof_e));
    }

    //Calcul de f(z) - e*vis
    let fz = f(za, zt, vis.clone(), g);
    let mut fz_moins_e_vis: Vec<Gr> = Vec::new();
    for i in 0..n {
        fz_moins_e_vis.push(fz[i] - e_vis[i]);
    }

    //Calcul de H(vis, (f(z) - e*vis), m)
    let mut total_str = "".to_string();
    for i in 0..vis.len() {
        total_str = total_str + &vis[i].to_string();
    }
    for i in 0..fz_moins_e_vis.len() {
        total_str = total_str + &fz_moins_e_vis[i].to_string();
    }

    let e = hash(&(total_str + m));


    //comparaison avec e
    e == proof_e
}

fn main() {
    //Creation du groupe g
    let mut rng = ark_std::test_rng();
    let g = Gr::rand(&mut rng);
    
    //numéro du prover
    let i=1;

    //Creation des Clefs privées et public
    let n = 10;
    let (sis, vis) = keygen(&mut rng, g, n);

    let m = "zejhfiuzehrkjfhezkhfezhrihzeifhzeiuhfpiuhzeifuh";
    //test avec la bonne clef privée
    let (e, za, zt) = prover(m, g, vis.clone(), sis[0], n, i);
    let res = verifier(m, g, vis.clone(), n, e, za.clone(), zt.clone());

    //test avec une mauvaise clef privée
    let false_si = ScalarField::rand(&mut rng);
    let (e2, za2, zt2) = prover(m, g, vis.clone(), false_si, n, i);
    let res2 = verifier(m, g, vis.clone(), n, e2, za2.clone(), zt2.clone());

    println!("Resultat de la vérification avec la bonne clé privée: {:?}", res);
    println!("Resultat de la vérification avec la mauvaise clé privée: {:?}", res2);
}