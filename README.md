# Research on destination passing style and linear types

```latex
\textbf{Proof.} By induction on the typing derivation.

\begin{itemize}

\item \textsc{TyTerm\_Val}: (0) $[[ G@ |- v : T ]]$\\
(0) gives (1) $[[v !! v | o]]$ immediately. From \textsc{TyEff\_NoEff} and \textsc{TyCmd\_Cmd} we conclude (2) $[[G@ |- v | e : T]]$.

\item \textsc{TyTerm\_App}: (0) $[[ m.G1@ µ G2@ |- t & u : T2 ]]$\\
We have\\
(1) $[[ G1@ |- t : T1 ]]$\\
(2) $[[ G2@ |- u : T1 m -> T2 ]]$\\
(3) $[[ G1@ disjoint G2@ ]]$\\
Using recursion hypothesis on (1) we get (4) $[[t !! v1 | e1]]$ where (5) $[[G1@ |- v1 | e1 : T1]]$.\\
Inverting \textsc{TyCmd\_Cmd} we get (5) $[[ G11@ µ G13@ |- v1 : T1 ]]$ and (6) $[[G12 u -G13@ ||- e1]]$ where (7) $[[G1@ = G11@ µ G12@]]$.\\
Using recursion hypothesis on (2) we get (8) $[[u !! v2 | e2]]$ where (9) $[[G2@ |- v2 | e2 : T1 m -> T2]]$.\\
Inverting \textsc{TyCmd\_Cmd} we get (10) $[[ G21@ µ G23@ |- v2 : T1 m -> T2 ]]$ and (11) $[[G22 u -G23@ ||- e2]]$ where (12) $[[G2@ = G21@ µ G22@]]$.\\
Using Lemma~\ref{lem:canonical} on (9) we get (13) $[[v2 = \x -> t']]$ and (14) $[[G21@ µ G23@ µ {x : m T1} |- t' : T2]]$.

\textit{Typing value part of the result}

Using Lemma~\ref{lem:subst} on (14) and (5) we get (15) $[[ m.(G11@ µ G13@) µ (G21@ µ G23@) |- t'[x := v1] : T2]]$.\\
Using recursion hypothesis on (15) we get (16) $[[t'[x := v1] !! v3 | e3]]$ where (17) $[[ m.(G11@ µ G13@) µ (G21@ µ G23@) |- v3 | e3: T2]]$.

\textit{Typing effect part of the result}

We have\\
(6) $[[G12@ u -G13@ ||- e1]]$ \\
(11) $[[G22@ u -G23@ ||- e2]]$

$[[G12@ disjoint G22@]]$ comes naturally from (3), (7) and (12).

We must show:\\
$[[G12@ disjoint G23@]]$: holes in $[[e2]]$ (associated to $[[u]]$) are fresh so they cannot match a destination name from $[[t]]$ as they don't exist yet when $[[t]]$ is evaluated.\\
$[[G22@ disjoint G13@]]$: slightly harder. Holes in $[[e1]]$ (associated to $[[t]]$) are fresh too, so I don't see a way for $[[u]]$ to create a term that could mention them, but sequentially, at least, they exist during $[[u]]$ evaluation. In fact, $[[G22]]$ might have intersection with $[[G13]]$ (see \textsc{TyEff\_Union}) as long as they share the same modalities (it's even harder to prove I think).\\
$[[G13@ disjoint G23@]]$: freshness of holes in both effects, executed sequentially, should be enough.

Let say this is solved by Lemma~\ref{lem:freshholes}, with no holes of $[[e1]]$ negative context appearing as dests in $[[e2]]$ positive context.

By \textsc{TyEff\_Union} we get (18) $[[G12@ µ G22@ u -G13@ µ -G23@ ||- e1 . e2]]$.\\
Inverting \textsc{TyCmd\_Cmd} on (17) we get (19) $[[m.(G111@ µ G131@) µ G211@ µ G231@ µ G3@ |- v3 : T2 ]]$ and (20) $[[m.(G112@ µ G132@) µ G212@ µ G232@ u -G3@ ||- e3 ]]$ where (21) $[[Gi1@ µ Gi2@ = Gi@ ]]$

We have\\
(18) $[[G12@ µ G22@ u -G13@ µ -G23@ ||- e1 . e2]]$\\
(20) $[[m.(G112@ µ G132@) µ G212@ µ G232@ u -G3@ ||- e3 ]]$\\

Using (21) on (18) to decompose $[[-G23@]]$, we get (22) $[[G12@ µ G22@ u -(G131@ µ G231@) µ -(G132@ µ G232@) ||- e1 . e2]]$

We want $[[G132@]]$ from (22) to cancel $[[m.G132@]]$ from (20), but the multiplicity doesn't match apparently.

$[[G13@]]$ contains dests associated to holes that may have been created when evaluation $[[t]]$ into $[[v1 | e1]]$. If $[[v1]]$ is used with delay (result of multiplying its context by $[[m]]$), then should we also delay the RHS of its associated effect?
In other terms, if we have $[[{@h:0 |T|n} |- @h' | h := Inl h']]$, and use $[[@h']]$ with delay $[[m]]$ (e.g stored inside another dest in the body of the function), should we also type the RHS of $[[h := Inl h']]$ with delay 1? I think so, if we want to keep the property that age of dests and age of the associated holes are the same. Which means a more refined substitution lemma.

\end{itemize}

\begin{lem}[Freshness of holes]\label{lem:freshholes}
Let $[[t]]$ be a program with no pre-existing ampar sharing hole names.

During the reduction of $[[t]]$, the only other place where the names of the holes on the RHS of an effect can appear is in the accompanying value of the command, as destinations.
\end{lem}
\begin{proof}
Names of the holes on the RHS of a new effect:
\begin{itemize}
  \item either are $\ottkw{fresh}$ (in all \textsc{BigStep\_Fill$\langle$\textnormal{\textit{Ctor}$\rangle$}} rules), which means the only other place where those names are known and can show up is as destinations on the accompanying value of the command ($[[G12]]$ in \textsc{TyCmd\_Cmd}), but not in positive or negative contexts of the command given by the evaluation of a sibling subterm;

    
  \item or are those of pre-existing holes coming from the extended value $[[w2]]$ of an ampar, when \textsc{BigStep\_FillComp} is evaluated. Because they come from an ampar, they must be neutralized by this ampar, so the left value $[[v1]]$ of the ampar is the only place where those names can show up, as destinations, if we disallow pre-existing ampar with shared hole names in the body of the initial program. And $[[v1]]$ is exactly the accompanying value returned by the evaluation of \textsc{BigStep\_FillComp}
  \end{itemize}

  \item TODO: prove that this property is preserved by typing rules
\end{proof}

\begin{thm}[Type safety for complete programs]
  If $[[ {} |- t : T ]]$ then $[[t !! v | o]]$ and $[[{} |- v : T]]$.
\end{thm}
\textbf{Proof.} By induction on the typing derivation.

\begin{itemize}

\item \textsc{TyTerm\_Val}: (0) $[[ G@ |- v : T ]]$\\
(0) gives (1) $[[v !! v | o]]$ immediately. From \textsc{TyEff\_NoEff} and \textsc{TyCmd\_Cmd} we conclude (2) $[[G@ |- v | e : T]]$.

\item \textsc{TyTerm\_App}: (0) $[[ m.G1@ µ G2@ |- t & u : T2 ]]$\\
We have\\
(1) $[[ G1@ |- t : T1 ]]$\\
(2) $[[ G2@ |- u : T1 m -> T2 ]]$\\
(3) $[[ G1@ disjoint G2@ ]]$\\
Using recursion hypothesis on (1) we get (4) $[[t !! v1 | e1]]$ where (5) $[[G1@ |- v1 | e1 : T1]]$.\\
Inverting \textsc{TyCmd\_Cmd} we get (5) $[[ G11@ µ G13@ |- v1 : T1 ]]$ and (6) $[[G12 u -G13@ ||- e1]]$ where (7) $[[G1@ = G11@ µ G12@]]$.\\
Using recursion hypothesis on (2) we get (8) $[[u !! v2 | e2]]$ where (9) $[[G2@ |- v2 | e2 : T1 m -> T2]]$.\\
Inverting \textsc{TyCmd\_Cmd} we get (10) $[[ G21@ µ G23@ |- v2 : T1 m -> T2 ]]$ and (11) $[[G22 u -G23@ ||- e2]]$ where (12) $[[G2@ = G21@ µ G22@]]$.\\
Using Lemma~\ref{lem:canonical} on (9) we get (13) $[[v2 = \x -> t']]$ and (14) $[[G21@ µ G23@ µ {x : m T1} |- t' : T2]]$.

\textit{Typing value part of the result}

Using Lemma~\ref{lem:subst} on (14) and (5) we get (15) $[[ m.(G11@ µ G13@) µ (G21@ µ G23@) |- t'[x := v1] : T2]]$.\\
Using recursion hypothesis on (15) we get (16) $[[t'[x := v1] !! v3 | e3]]$ where (17) $[[ m.(G11@ µ G13@) µ (G21@ µ G23@) |- v3 | e3: T2]]$.

\textit{Typing effect part of the result}

We have\\
(6) $[[G12@ u -G13@ ||- e1]]$ \\
(11) $[[G22@ u -G23@ ||- e2]]$

$[[G12@ disjoint G22@]]$ comes naturally from (3), (7) and (12).

We must show:\\
$[[G12@ disjoint G23@]]$: holes in $[[e2]]$ (associated to $[[u]]$) are fresh so they cannot match a destination name from $[[t]]$ as they don't exist yet when $[[t]]$ is evaluated.\\
$[[G22@ disjoint G13@]]$: slightly harder. Holes in $[[e1]]$ (associated to $[[t]]$) are fresh too, so I don't see a way for $[[u]]$ to create a term that could mention them, but sequentially, at least, they exist during $[[u]]$ evaluation. In fact, $[[G22]]$ might have intersection with $[[G13]]$ (see \textsc{TyEff\_Union}) as long as they share the same modalities (it's even harder to prove I think).\\
$[[G13@ disjoint G23@]]$: freshness of holes in both effects, executed sequentially, should be enough.

Let say this is solved by Lemma~\ref{lem:freshholes}, with no holes of $[[e1]]$ negative context appearing as dests in $[[e2]]$ positive context.

By \textsc{TyEff\_Union} we get (18) $[[G12@ µ G22@ u -G13@ µ -G23@ ||- e1 . e2]]$.\\
Inverting \textsc{TyCmd\_Cmd} on (17) we get (19) $[[m.(G111@ µ G131@) µ G211@ µ G231@ µ G3@ |- v3 : T2 ]]$ and (20) $[[m.(G112@ µ G132@) µ G212@ µ G232@ u -G3@ ||- e3 ]]$ where (21) $[[Gi1@ µ Gi2@ = Gi@ ]]$

We have\\
(18) $[[G12@ µ G22@ u -G13@ µ -G23@ ||- e1 . e2]]$\\
(20) $[[m.(G112@ µ G132@) µ G212@ µ G232@ u -G3@ ||- e3 ]]$\\

Using (21) on (18) to decompose $[[-G23@]]$, we get (22) $[[G12@ µ G22@ u -(G131@ µ G231@) µ -(G132@ µ G232@) ||- e1 . e2]]$

We want $[[G132@]]$ from (22) to cancel $[[m.G132@]]$ from (20), but the multiplicity doesn't match apparently.

$[[G13@]]$ contains dests associated to holes that may have been created when evaluation $[[t]]$ into $[[v1 | e1]]$. If $[[v1]]$ is used with delay (result of multiplying its context by $[[m]]$), then should we also delay the RHS of its associated effect?
In other terms, if we have $[[{@h:0 |T|n} |- @h' | h := Inl h']]$, and use $[[@h']]$ with delay $[[m]]$ (e.g stored inside another dest in the body of the function), should we also type the RHS of $[[h := Inl h']]$ with delay 1? I think so, if we want to keep the property that age of dests and age of the associated holes are the same. Which means a more refined substitution lemma.

\end{itemize}

\begin{lem}[Freshness of holes]\label{lem:freshholes}
Let $[[t]]$ be a program with no pre-existing ampar sharing hole names.

During the reduction of $[[t]]$, the only other place where the names of the holes on the RHS of an effect can appear is in the accompanying value of the command, as destinations.
\end{lem}
\begin{proof}
Names of the holes on the RHS of a new effect:
\begin{itemize}
  \item either are $\ottkw{fresh}$ (in all \textsc{BigStep\_Fill$\langle$\textnormal{\textit{Ctor}$\rangle$}} rules), which means the only other place where those names are known and can show up is as destinations on the accompanying value of the command ($[[G12]]$ in \textsc{TyCmd\_Cmd}), but not in positive or negative contexts of the command given by the evaluation of a sibling subterm;

    
  \item or are those of pre-existing holes coming from the extended value $[[w2]]$ of an ampar, when \textsc{BigStep\_FillComp} is evaluated. Because they come from an ampar, they must be neutralized by this ampar, so the left value $[[v1]]$ of the ampar is the only place where those names can show up, as destinations, if we disallow pre-existing ampar with shared hole names in the body of the initial program. And $[[v1]]$ is exactly the accompanying value returned by the evaluation of \textsc{BigStep\_FillComp}
  \end{itemize}

  \item TODO: prove that this property is preserved by typing rules
\end{proof}
```
