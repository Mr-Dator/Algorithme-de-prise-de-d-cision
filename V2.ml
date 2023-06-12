(*  Quelques fonctions avancées pour les calculs staatistiques
    Copyright (C) 2011 Will M. Farr <w-farr@northwestern.edu>
*)
#load "graphics.cma";;(*Librairie pour la fenêtre Graphique*)
open Graphics;;
Random.self_init;

let mean xs = 
  let sum = ref 0.0 and
      n = Array.length xs in 
    for i = 0 to n - 1 do 
      sum := !sum +. xs.(i)
    done;
    !sum /. (float_of_int n) in

(* Method from Press, Teukolsky, Vetterling and Flannery.  Numerical
   Recipes.  Cambridge University Press, 2007 (third edition).
   Section 7.3.9; original algorithm by Leva.*)
let draw_gaussian mu sigma = 
  let rec loop () = 
    let u = Random.float 1.0 and 
        v = 1.7156 *. (Random.float 1.0 -. 0.5) in 
    let x = u -. 0.449871 and 
        y = abs_float v +. 0.386595 in 
    let q = x*.x +. y*.(0.19600*.y -. 0.25472*.x) in 
      if q > 0.27597 && (q > 0.27846 || v*.v > (-4.0)*.(log u)*.u*.u) then 
        loop ()
      else
        mu +. sigma*.v/.u in 
    loop () in

let draw_uniform a b = 
  let d = b -. a in 
    a +. d*.(Random.float 1.0) in

(*Fonctions de gestion de graphe *)

let nouveauGraphe n =
	let f i = (0,[]) in
	Array.init n f in

let sontAdjacents g x y = 
	let rec aux t x = match t with
	[] -> false
	|a::q -> if a=x then true else aux q x 
	in
	let v,l= g.(y) in aux l x; in

let ajouterArete g x y =
	let t = Array.length g in
	if x >= t || y>=t then failwith "Sommet absent" else begin 
	if not (sontAdjacents g x y) then begin 
	g.(x) <- (fst g.(x),y::snd g.(x)); 
	g.(y) <- (fst g.(y),x::snd g.(y)) end else () end in

let supprimerArete g x y =
	let rec aux t x = match t with
		[] ->[]
		|a::q -> if x=a then q else a::aux q x 
	in
	if sontAdjacents g x y then 
	begin 
	g.(x) <- fst g.(x), aux (snd g.(x)) y; 
	g.(y) <- fst g.(y), aux (snd g.(y)) x 
	end 
	else failwith"Il n'y pas d'arete a supprimer" in

let existe g x = x < Array.length g in

let voisins g x = if existe g x then snd g.(x) else failwith "Sommet absent" in

let valeurSommet g x = if existe g x then fst g.(x) else failwith"Sommet absent" in

let changerValeur g x v = if existe g x then g.(x) <- v,snd g.(x) in

(*Parametres de l'epideime*)

let pContamination = 0.650 in
let pContaEff = ref pContamination in
let dureeRetablissement = 50 in
let dureeIncubation = 5 in
let letalite = 0.01 in
let reinfecter = 0.00 in

(*Paramtres du graphe*)

let progression = ref 0. in
let iterationCycle = 1 in
let dimFenetre = 750 in
let population = 5000 in
let nombreMoyenDeVoisins = 10 in 
let ecartAlaMoyenne = int_of_float ((draw_gaussian 10. 10. -. 10.)/.10.) in
let listeConta = ref [] in
let listeInf = ref [] in
let listeRetablis = ref [] in
let initialementInf = 0.01 in 

let infectes = ref 0 in (*Nombre d'infectés *)
let morts = ref 0 in (*Nombre d'infectés morts*)
let retablis = ref 0 in (*Nombre d'infectés guéris*)
let sains = ref (population - !infectes - !morts) in (*Variable non nécessaire; présente pour la clareté*)
let contamines = ref 0 in
let testsPositifs = 1. in
 
(*EXTRACTIONS DES DONNES UTILES*)

let statsInfectes = Array.make dimFenetre 0 in
let statsRet = Array.make dimFenetre 0 in
let statsDec = Array.make dimFenetre 0 in
let intervalleSeriel = 4. in (*entre 4 et 8 pour le COVID*)
let calculTauxIncidence t = if t > 0 then float_of_int statsInfectes.(t) *. testsPositifs /. float_of_int population else 0. in
let statsIncidence = Array.make dimFenetre 0. in
let sommeTx = ref 0. in
let calculR t = if t = 0 then 0. else (*R = newinf/new rec + New Deaths*)
	(*sommeTx := !sommeTx +. statsIncidence.(t-1);
	statsIncidence.(t) /. (!sommeTx *. intervalleSeriel) end *)
	1. +. float_of_int(statsInfectes.(t) - statsInfectes.(t-1)) /. float_of_int(statsRet.(t) - statsRet.(t-1) + statsDec.(t) - statsDec.(t-1))
	in
let statsR = Array.make dimFenetre 0. in
let statsRGlissant = Array.make dimFenetre 0. in
let calculRGlissant t n = 
	let r = ref 0. in 
	for k = 0 to n-1 do
		if t-k >= 0 then r := !r +. statsR.(t-k);
	done;
	!r/. float_of_int n in
 
(*Initialisation du graphe*)

let simulation = nouveauGraphe population, Array.init population (fun i -> [|0|]) in(*La population est modélisée par une paire graphe, liste des attributs des sommets*)

for k = 0 to population - 1 do
	for l = 0 to nombreMoyenDeVoisins + ecartAlaMoyenne do
		ajouterArete (fst simulation) k (Random.int population);
	done;
done;

let rec ajouterListe x l = match l with
	[] -> [x]
	|a::q -> if a = x then ajouterListe x q else a::ajouterListe x q in

let rec supprimerListe x l = match l with
	[] -> []
	|a::q -> if a = x then supprimerListe x q else a::supprimerListe x q in
 
let etat x t = 
	if abs x > Array.length t -1 then failwith "Sommet invalide"
	else t.(x).(0) in

let contamineSommet x tableauAttributs = 
	if (etat x tableauAttributs) = 0 then begin 
		tableauAttributs.(x).(0) <- 1; 
		incr contamines;
		decr sains; end else () in 

let rec contamineVoisins l tableauAttributs = match l with
	[] -> ()
	|a::q -> if (etat a tableauAttributs )= 0 && (Random.float 1.) <= !pContaEff then begin
	contamineSommet a tableauAttributs;
	listeConta := ajouterListe a !listeConta;
	contamineVoisins q tableauAttributs;
	end
	else contamineVoisins q tableauAttributs
	in 
	
let acc = ref 0 in

let rec incubation l listeSecondaire tableauAttributs = match l with 
	[] -> []
	|a::q -> if etat a tableauAttributs >= 1 + dureeIncubation then 
				begin listeSecondaire := a::!listeSecondaire;
						incr infectes;
						incr acc;
						decr contamines;
						incubation q listeSecondaire tableauAttributs;
				end
				else begin tableauAttributs.(a).(0) <- (tableauAttributs.(a).(0) + 1);
				a::incubation q listeSecondaire tableauAttributs end in 
				
let rec retablissement l listeSecondaire tableauAttributs = match l with 
	[] -> []
	|a::q -> if etat a tableauAttributs >= 1 + dureeIncubation + dureeRetablissement then 
				begin listeSecondaire := a::!listeSecondaire;
						decr infectes;
						incr retablis;
						retablissement q listeSecondaire tableauAttributs;
				end
				else begin tableauAttributs.(a).(0) <- (tableauAttributs.(a).(0) + 1);
				a::retablissement q listeSecondaire tableauAttributs; end in 

let rec parcours l  = match l with
		[] -> ()
		|a::q -> contamineVoisins (voisins (fst simulation) a) (snd simulation) in

let cycle () = 
	listeConta := incubation !listeConta listeInf (snd simulation);
	listeInf := retablissement !listeInf listeRetablis (snd simulation);
	parcours !listeInf;
	in 

let rec read l = match l with
	[] -> ()
	|a::q -> (print_int a; print_newline(); read q) in

let initialise () = 
	for k = 0 to int_of_float (initialementInf *. float_of_int population) - 1 do 
		let n = Random.int population in 
		contamineSommet n (snd simulation);
		listeConta := ajouterListe n !listeConta;
		done; in

let rEff = ref 1. in

let rObj = 0.5 in

let ecart = 0.1 in

let effets = [|0.95;0.90;0.85;0.70;0.60;0.55;0.50;0.40;0.30;0.15|] in

let couts = [|1;2;3;5;7;9;10;15;20;30|] in

let nouveauGrapheBis n =
	let f i = (-1.,[]) in
	Array.init n f in

let graphe = nouveauGrapheBis 1024 in

let pow2 = [|1;2;4;8;16;32;64;128;256;1024|] in

let etatActuel = ref 0 in

let arrayToNUplet t = t.(0),t.(1),t.(2),t.(3),t.(4),t.(5),t.(6),t.(7),t.(8),t.(9) in

let nUpletToNumber q = 
	let q,w,e,r,t,y,u,i,o,p = q in
	(p+2*(o+2*(i+2*(u+2*(y+2*(t+2*(r+2*(e+2*(w+2*q))))))))) in

let numberToNUplet n = 
	let t = Array.make 10 0 in
	let c = ref n in
	for k = 0 to 9 do
		t.(10-k-1)<- !c mod 2;
		c := !c/2;
	done; arrayToNUplet t in
	
let alt q n = 
	let q,w,e,r,t,y,u,i,o,p = q in
	let a= Array.make 10 0 in
	a.(0) <- q;
	a.(1) <- w;
	a.(2) <- e;
	a.(3) <- r;
	a.(4) <- t;
	a.(5) <- y;
	a.(6) <- u;
	a.(7) <- i;
	a.(8) <- o;
	a.(9) <- p;
	a.(n) <- (a.(n) + 1) mod 2; arrayToNUplet a in
	
for i = 0 to 1023 do
	for j = 0 to 9 do
		ajouterArete graphe i (nUpletToNumber (alt (numberToNUplet i) j));
	done;
done;

let rec evalueEtat l robj ecart r = match l with 
	[] -> -1
	|(r,i)::q -> if robj +. ecart > r && robj -. ecart < r then i else evalueEtat q robj ecart r in

let etatSup i = match numberToNUplet i with
	0,_,_,_,_,_,_,_,_,_ -> i + pow2.(9)
	|_,0,_,_,_,_,_,_,_,_ -> i + pow2.(8)
	|_,_,0,_,_,_,_,_,_,_ -> i + pow2.(7)
	|_,_,_,0,_,_,_,_,_,_ -> i + pow2.(6)
	|_,_,_,_,0,_,_,_,_,_ -> i + pow2.(5)
	|_,_,_,_,_,0,_,_,_,_ -> i + pow2.(4)
	|_,_,_,_,_,_,0,_,_,_ -> i + pow2.(3)
	|_,_,_,_,_,_,_,0,_,_ -> i + pow2.(2)
	|_,_,_,_,_,_,_,_,0,_ -> i + pow2.(1)
	|_,_,_,_,_,_,_,_,_,0 -> i + pow2.(0)
	|_,_,_,_,_,_,_,_,_,_ -> i
	in

let etatInf i = match numberToNUplet i with
	_,_,_,_,_,_,_,_,_,1 -> i - pow2.(0)
	|_,_,_,_,_,_,_,_,1,_ -> i - pow2.(1)
	|_,_,_,_,_,_,_,1,_,_ -> i - pow2.(2)
	|_,_,_,_,_,_,1,_,_,_ -> i - pow2.(3)
	|_,_,_,_,_,1,_,_,_,_ -> i - pow2.(4)
	|_,_,_,_,1,_,_,_,_,_ -> i - pow2.(5)
	|_,_,_,1,_,_,_,_,_,_ -> i - pow2.(6)
	|_,_,1,_,_,_,_,_,_,_ -> i - pow2.(7)
	|_,1,_,_,_,_,_,_,_,_ -> i - pow2.(8)
	|1,_,_,_,_,_,_,_,_,_ -> i - pow2.(9)
	|_,_,_,_,_,_,_,_,_,_ -> i
	in

let effet probaConta etat = 
	let q,w,e,r,t,y,u,i,o,p = numberToNUplet etat in
	pContaEff := probaConta;
	pContaEff := !pContaEff *. effets.(0)*.float_of_int q;
	pContaEff := !pContaEff *. effets.(1)*.float_of_int w;
	pContaEff := !pContaEff *. effets.(2)*.float_of_int e;
	pContaEff := !pContaEff *. effets.(3)*.float_of_int r;
	pContaEff := !pContaEff *. effets.(4)*.float_of_int t;
	pContaEff := !pContaEff *. effets.(5)*.float_of_int y;
	pContaEff := !pContaEff *. effets.(6)*.float_of_int u;
	pContaEff := !pContaEff *. effets.(7)*.float_of_int i;
	pContaEff := !pContaEff *. effets.(8)*.float_of_int o;
	pContaEff := !pContaEff *. effets.(9)*.float_of_int p;
	in

let transition g r robj ecart etat = 
	changerValeur g etat r;
	let q = (*evalueEtat (voisinsBis g etat) robj ecart r*) -1 in
	if q = -1 then begin 
		if r > robj +. ecart then etatActuel := etatSup etat
		else if r < robj -. ecart then etatActuel := etatInf etat
		else ()
		end
	else etatActuel := q; in

let prepDraw a taille =
	let g i =  a.(i) in
	let f i = (i, g i) in
	let courbe = Array.init taille f in courbe in

let a = Array.make dimFenetre 0 in

let b = Array.make dimFenetre 0 in

let c = Array.make dimFenetre 0 in

let d = Array.make dimFenetre 0 in

let e = Array.make dimFenetre 0 in

let f = Array.make dimFenetre 0 in

let p = Array.make dimFenetre 0 in

let q = Array.make dimFenetre 0 in

open_graph(" "^string_of_int dimFenetre ^"x"^ string_of_int (dimFenetre + 1)); (*1px= 1 unité*)

initialise ();

	for k  = 0 to (dimFenetre-1) do
	a.(k) <- (int_of_float(Float.round(float_of_int population *. float_of_int dimFenetre /. float_of_int population)));

	b.(k) <- (int_of_float(Float.round(float_of_int !sains *. float_of_int dimFenetre /. float_of_int population)));

	c.(k) <- (int_of_float(Float.round(float_of_int !contamines *. float_of_int dimFenetre /. float_of_int population)));

	d.(k) <- (int_of_float(Float.round(float_of_int !infectes *. float_of_int dimFenetre /. float_of_int population)));

	e.(k) <- (int_of_float(Float.round(float_of_int !retablis *. float_of_int dimFenetre /. float_of_int population)));

	f.(k) <- (int_of_float(Float.round(float_of_int !morts *. float_of_int dimFenetre /. float_of_int population)));
	
	statsInfectes.(k) <- !infectes;
	
	statsIncidence.(k) <- calculTauxIncidence k;
	
	statsRet.(k) <- !retablis;
	
	statsR.(k) <- calculR k;
	
	rEff := calculRGlissant k 7;
	
	transition graphe !rEff rObj ecart !etatActuel;
	
	statsRGlissant.(k) <- calculRGlissant k 7;
	q.(k) <- (int_of_float(Float.round(statsRGlissant.(k) *. float_of_int dimFenetre /. 8.)));
	
	effet pContamination !etatActuel;
	
	for j = 0 to iterationCycle-1 do
		cycle();
		progression := !progression +. 100./.(float_of_int (iterationCycle* dimFenetre));
		print_float !progression;
		print_string "%";
		print_newline();
		done;
	done;

let courbepop = prepDraw a dimFenetre in

let courbesains = prepDraw b dimFenetre in

let courbeconta = prepDraw c dimFenetre in

let courbeinf = prepDraw d dimFenetre in

let courberet = prepDraw e dimFenetre in

let courbemorts = prepDraw f dimFenetre in

let courbeR = prepDraw q dimFenetre in

set_color black;
draw_poly_line courbepop;
moveto(4*dimFenetre/5) (2*dimFenetre/3);
draw_string "Population";

set_color blue;
draw_poly_line courbesains;
moveto(4*dimFenetre/5) (2*dimFenetre/3 - dimFenetre/18);
draw_string "Sains";

set_color green;
draw_poly_line courbeconta;
moveto(4*dimFenetre/5) (2*dimFenetre/3 - 2*dimFenetre/18);
draw_string "Contaminés";

set_color red;
draw_poly_line courbeinf;
moveto(4*dimFenetre/5) (2*dimFenetre/3 - 3*dimFenetre/18);
draw_string "Infectés";

set_color magenta;
draw_poly_line courberet;
moveto(4*dimFenetre/5) (2*dimFenetre/3 - 4*dimFenetre/18);
draw_string "Rétablis";

set_color cyan;
draw_poly_line courbemorts;
moveto(4*dimFenetre/5) (2*dimFenetre/3 - 5*dimFenetre/18);
draw_string "Décès";

(*set_color yellow;
draw_poly_line courbeR;*)
statsRGlissant;;
