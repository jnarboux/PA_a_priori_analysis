# Proof assistant for undergraduate mathematics education: elements of a priori analysis

The repositoty contains accompanying files for the paper "Proof assistants for undergraduate mathematics and computer science education: elements of a priori analysis"

This paper presents an a-priori analysis of the use of five different interactive proof assistants for education, based on the resolution of a typical undergraduate exercise on abstract functions. It proposes to analyse these tools according to three main categories of aspects: language and interaction mode, automation and user assistance, and proof structure and visualisation. We argue that this analysis may help formulate and clarify further research questions on the possible impact of such tools on the development of reasoning and proving skills.

## Case study

For formalize the following two exercises using several proof assistants.

Given f:A→B and C⊆A, show that C⊆f^(-1) (f(C)).

Given f:A→B and C⊆A, show that if f is injective then f^(-1) (f(C))⊆C.

List of proof assistants we experimented with:
- [Coq](coq.inria.fr), using tactics [case_study.v](Coq/case_study.v)
- [Isabelle](https://isabelle.in.tum.de/), using the Isar declarative language [case_study.thy](Isabelle/case_study.thy)
- [Lurch](https://lurchmath.github.io/lurch/site/), using controlled natural language [case_study.lurch](Lurch/case_study.lurch)
- [Edukera](edukera.com), using a point and click user interface
- [DEAduction](https://github.com/dEAduction/dEAduction), using a point and click user interface built above Lean

## Screenshots

### DEAduction

### Isabelle/HOL

The proof formalized without using automation using the Isar language:

![ISABELLE_PROOF](https://user-images.githubusercontent.com/1147773/162236526-ad92ea78-2f30-4ce3-be75-eb3f88aa51c9.png)

### Edukera

The popup window when clicking on a definition:

<img width="839" alt="Screenshot Edukera Popup" src="https://user-images.githubusercontent.com/1147773/162251820-47ce23e6-bff7-4052-9ce3-5cc3bc3b0f8c.png">

During the proof:

<img width="839" alt="Screenshot Edukera (unfinished proof)" src="https://user-images.githubusercontent.com/1147773/162251236-7183bfca-f0ff-4b0c-99d0-0f1adc387247.png">

An option is also available to display the proof tree:

![edukera proof tree](https://user-images.githubusercontent.com/1147773/162238716-bc035556-6843-42df-b67a-315428bda5b9.png)

### Lurch

<img width="1114" alt="Lurch screenshot (properties and direct implication, with validation)" src="https://user-images.githubusercontent.com/12487671/162261048-fb53fef3-5147-490d-879b-c0369ad376b6.png">

<img width="1114" alt="Lurch screenshot (converse, with injectivity, with validation)" src="https://user-images.githubusercontent.com/12487671/162261115-a110d3ff-3e6c-4bf3-8200-4233dfc3504b.png">

## Videos



## Authors

 - Evmorfia Iro Bartzia
 - Antoine Meyer
 - Julien Narboux
