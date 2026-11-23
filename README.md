<div align="center">

# L∃∀N 4

**From First Proof to Formalized Mathematics**<br>
*De la première preuve aux mathématiques formalisées*

A free book to learn Lean, from your first proof to formalized analysis, in English and French.

**[Download the PDF](Book/LEAN4_From_First_Proof_to_Formalized_Mathematics.pdf)** (English, 287 pages) · **[Télécharger le PDF](Book/LEAN4_De_la_premiere_preuve_aux_mathematiques_formalisees.pdf)** (français, 304 pages)

![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0-0d9488)
![Mathlib v4.35.0](https://img.shields.io/badge/Mathlib-v4.35.0-0d9488)
![Licence CC BY-NC-ND 4.0](https://img.shields.io/badge/licence-CC%20BY--NC--ND%204.0-555555)
![Version November 2026](https://img.shields.io/badge/version-November%202026-555555)

[English](#about-the-book) · [Version française](#version-française)

</div>

## About the book

This book teaches Lean 4 from installation to formalized analysis, with every example written for Lean 4.35.0 and the matching Mathlib release.

- **Who it is for:** a working mathematician or a strong student. It assumes no type theory and no functional programming.
- **Where it goes:** from a first proof to inequalities, sums, limits, derivatives and integrals in Mathlib.
- **Every example checked:** each code block behaves as the book shows, and the examples come as Lean files (see [The examples](#the-examples)).
- **Practice:** exercises with solutions in 24 of the 27 chapters.
- **Reference:** appendices on which tactic to use when, Unicode input, common error messages, a glossary, and every tactic in alphabetical order.

By Claude, supervised by Chadi SABA ([how this book was written](#how-this-book-was-written)).

## Contents

| Part | Chapters | Topics |
|---|:---:|---|
| I. Getting Oriented | 1–4 | What Lean is, installing it, setting up VS Code, your first hour |
| II. The Language and Its Logic | 5–11 | Types and functions, propositions, tactics, rewriting, induction, structures, dependent types |
| III. Mathematics with Mathlib | 12–20 | Finding lemmas, automation, casts, sets and sums, algebra, limits and topology, calculus, integration, a worked project |
| IV. Lean as a Programming Language | 21–23 | Functional programming, verified programs, metaprogramming |
| V. Working Practice | 24–27 | Projects and Lake, proof engineering, AI tools, the community |

<details>
<summary>All chapters</summary>

**Part I — Getting Oriented**

1. What Lean Is
2. Installing Lean and Starting a Project
3. Setting Up VS Code Properly
4. Your First Hour in the Editor

**Part II — The Language and Its Logic**

5. Terms, Types and Functions
6. Propositions and Proofs
7. Tactics, the Core Toolkit
8. Equality, Rewriting and calc
9. Inductive Types, Recursion and Induction
10. Structures and Type Classes
11. Dependent Type Theory, One Level Deeper

**Part III — Mathematics with Mathlib**

12. Finding Things in Mathlib
13. Automation
14. Numbers, Casts and Their Traps
15. Sets, Functions, Finsets and Sums
16. Algebraic Structures
17. Filters, Limits and Topology
18. Calculus
19. Measure Theory and Integration
20. A Worked Project in Analysis

**Part IV — Lean as a Programming Language**

21. Functional Programming and Effects
22. Verified Programs
23. Metaprogramming

**Part V — Working Practice**

24. Projects, Lake, and Keeping Up with Mathlib
25. Proof Engineering
26. Lean and AI Tools
27. Community, Contributing, and Where to Go Next

**Appendices:** A. Which Tactic When · B. Unicode Abbreviations · C. Common Error Messages · D. Glossary · E. Every Tactic, Alphabetically

</details>

## The examples

[Book_Examples](Book_Examples) holds every Lean example of the book: 84 files in reading order, from `Ch01_1.lean` to `Ch27_4.lean`. A line before each example gives its page in both editions. Open these files in your Lean project instead of copying code from the PDF. Both editions share the same code; the comments in the files are in English.

<details>
<summary>Check that every example compiles (Windows)</summary>

1. Download this repository (**Code → Download ZIP**) and unzip it.
2. Copy the `Book_Examples` folder into your Lean project, next to `lakefile.toml`. The project must use Lean 4.35.0 and Mathlib v4.35.0, with Mathlib downloaded (`lake exe cache get`).
3. Double-click `run_check.bat`. The check takes about 10 to 20 minutes. For one chapter only, open a terminal in `Book_Examples` and type `run_check.bat -Only Ch07`.
4. Read `Book_Examples\report.txt`: **OK** means as in the book, **FAIL** a block that is not, **DIFF** a printed result that differs, **NOTE** an exercise that shows errors until it is solved.

[reference_report.txt](Book_Examples/reference_report.txt) is the result of this check with Lean 4.35.0 and the Mathlib v4.35.0 modules the book uses: 400 of 400 code blocks and 238 of 238 printed results as in the book. Five blocks are not compiled: a piece of a proof, `#loogle` and `#leansearch` (they need the internet), and two files of the sample project.

</details>

## The tactic sheet

[TacticSheet](TacticSheet) holds the tactics of Chapter 7 on two printable A4 pages: [English](TacticSheet/Lean_4_Tactics.pdf) · [français](TacticSheet/Tactiques_Lean_4.pdf).

## How this book was written

This book was written by Claude, an AI model made by Anthropic. Dr. Chadi SABA conceived the project, guided the writing through successive prompts, chose what to keep, and takes responsibility for the published text.

## How to cite

L∃∀N 4: From First Proof to Formalized Mathematics, by Claude, supervised by Chadi SABA, version of November 2026, https://csaba.perso.math.cnrs.fr/.

<details>
<summary>BibTeX</summary>

```bibtex
@misc{lean4firstproof,
  title  = {L$\exists\forall$N 4: From First Proof
            to Formalized Mathematics},
  author = {{Claude (Anthropic)}},
  note   = {Supervised by Chadi SABA. Version of November 2026},
  year   = {2026},
  howpublished = {\url{https://csaba.perso.math.cnrs.fr/}}
}
```

</details>

## Licence and contact

This book is free. You may read, copy, print and share it, unchanged and with this notice, but you may not sell it or share a modified version ([CC BY-NC-ND 4.0](LICENSE)).

To report an error or suggest a change, write to Dr. SABA at chadi.saba@unilim.fr.<br>
Personal website: [csaba.perso.math.cnrs.fr](https://csaba.perso.math.cnrs.fr/)

---

## Version française

**L∃∀N 4 : De la première preuve aux mathématiques formalisées** · [Télécharger le PDF](Book/LEAN4_De_la_premiere_preuve_aux_mathematiques_formalisees.pdf) · 304 pages

Ce livre enseigne Lean 4, de l’installation jusqu’à l’analyse formalisée, avec des exemples tous écrits pour Lean 4.35.0 et la version de Mathlib qui lui correspond.

- **Pour qui :** un mathématicien en activité ou un étudiant solide. Il ne suppose aucune connaissance de la théorie des types ni de la programmation fonctionnelle.
- **Jusqu’où :** de la première preuve aux inégalités, sommes, limites, dérivées et intégrales avec Mathlib.
- **Tous les exemples vérifiés :** chaque bloc de code se comporte comme le livre le montre, et les exemples sont fournis en fichiers Lean.
- **De la pratique :** des exercices avec leurs solutions dans 24 des 27 chapitres.

Par Claude, sous la direction de Chadi SABA.

| Partie | Chapitres | Thèmes |
|---|:---:|---|
| I. Premiers repères | 1–4 | Ce qu’est Lean, l’installer, configurer VS Code, votre première heure |
| II. Le langage et sa logique | 5–11 | Types et fonctions, propositions, tactiques, réécriture, récurrence, structures, types dépendants |
| III. Les mathématiques avec Mathlib | 12–20 | Trouver des lemmes, automatisation, conversions, ensembles et sommes, algèbre, limites et topologie, calcul différentiel, intégration, un projet complet |
| IV. Lean comme langage de programmation | 21–23 | Programmation fonctionnelle, programmes vérifiés, métaprogrammation |
| V. La pratique au quotidien | 24–27 | Projets et Lake, ingénierie de la preuve, outils d’IA, la communauté |

<details>
<summary>Tous les chapitres</summary>

**Partie I — Premiers repères**

1. Ce qu’est Lean
2. Installer Lean et créer un projet
3. Bien configurer VS Code
4. Votre première heure dans l’éditeur

**Partie II — Le langage et sa logique**

5. Termes, types et fonctions
6. Propositions et preuves
7. Les tactiques, la boîte à outils de base
8. Égalité, réécriture et calc
9. Types inductifs, récursion et récurrence
10. Structures et classes de types
11. Théorie des types dépendants, un cran plus loin

**Partie III — Les mathématiques avec Mathlib**

12. Trouver ce qu’il faut dans Mathlib
13. Automatisation
14. Nombres, conversions et leurs pièges
15. Ensembles, fonctions, finsets et sommes
16. Structures algébriques
17. Filtres, limites et topologie
18. Calcul différentiel
19. Théorie de la mesure et intégration
20. Un projet complet en analyse

**Partie IV — Lean comme langage de programmation**

21. Programmation fonctionnelle et effets
22. Programmes vérifiés
23. Métaprogrammation

**Partie V — La pratique au quotidien**

24. Projets, Lake et suivre l’évolution de Mathlib
25. Ingénierie de la preuve
26. Lean et les outils d’IA
27. Communauté, contributions et suite du parcours

**Annexes :** A. Quelle tactique, quand · B. Abréviations Unicode · C. Messages d’erreur courants · D. Glossaire · E. Toutes les tactiques, par ordre alphabétique

</details>

### Les exemples

[Book_Examples](Book_Examples) contient tous les exemples Lean du livre : 84 fichiers, dans l’ordre de lecture, de `Ch01_1.lean` à `Ch27_4.lean`. Une ligne avant chaque exemple donne sa page dans les deux éditions (« French edition » pour celle-ci). Ouvrez ces fichiers dans votre projet Lean au lieu de copier le code depuis le PDF. Le code est le même dans les deux éditions ; les commentaires des fichiers sont en anglais.

<details>
<summary>Vérifier que chaque exemple compile (Windows)</summary>

1. Téléchargez ce dépôt (**Code → Download ZIP**) et décompressez-le.
2. Copiez le dossier `Book_Examples` dans votre projet Lean, à côté de `lakefile.toml`. Le projet doit utiliser Lean 4.35.0 et Mathlib v4.35.0, après avoir téléchargé Mathlib (`lake exe cache get`).
3. Double-cliquez sur `run_check.bat`. La vérification prend de 10 à 20 minutes. Pour un seul chapitre, ouvrez un terminal dans `Book_Examples` et tapez `run_check.bat -Only Ch07`.
4. Lisez `Book_Examples\report.txt` : **OK** signifie comme dans le livre, **FAIL** un bloc qui ne l’est pas, **DIFF** un résultat affiché qui diffère, **NOTE** un exercice qui montre des erreurs tant qu’il n’est pas résolu.

[reference_report.txt](Book_Examples/reference_report.txt) (en anglais) donne le résultat de cette vérification avec Lean 4.35.0 et les modules de Mathlib v4.35.0 qu’utilise le livre : 400 blocs de code sur 400 et 238 résultats affichés sur 238 conformes au livre.

</details>

### La fiche des tactiques

[TacticSheet](TacticSheet) rassemble les tactiques du chapitre 7 sur deux pages A4 à imprimer : [français](TacticSheet/Tactiques_Lean_4.pdf) · [English](TacticSheet/Lean_4_Tactics.pdf).

### Comment ce livre a été écrit

Ce livre a été écrit, puis traduit en français, par Claude, un modèle d’IA développé par Anthropic. Le Dr Chadi SABA a conçu le projet, guidé la rédaction par des requêtes successives, choisi ce qu’il fallait garder, et assume la responsabilité du texte publié.

### Comment citer ce livre

L∃∀N 4 : De la première preuve aux mathématiques formalisées, par Claude, sous la direction de Chadi SABA, version de novembre 2026, https://csaba.perso.math.cnrs.fr/.

<details>
<summary>BibTeX</summary>

```bibtex
@misc{lean4premierepreuve,
  title  = {L$\exists\forall$N 4 : De la première preuve
            aux mathématiques formalisées},
  author = {{Claude (Anthropic)}},
  note   = {Sous la direction de Chadi SABA. Version de novembre 2026},
  year   = {2026},
  howpublished = {\url{https://csaba.perso.math.cnrs.fr/}}
}
```

</details>

### Licence et contact

Ce livre est gratuit. Vous pouvez le lire, le copier, l’imprimer et le partager, sans le modifier et en conservant cette mention, mais vous ne pouvez ni le vendre ni diffuser une version modifiée ([licence CC BY-NC-ND 4.0](LICENSE)).

Pour signaler une erreur ou proposer une modification, écrivez au Dr SABA à chadi.saba@unilim.fr.<br>
Site personnel : [csaba.perso.math.cnrs.fr](https://csaba.perso.math.cnrs.fr/)
