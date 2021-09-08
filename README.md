# Proving Brower Fixed Point Theorem in Lean

The blueprint was forked from [liquid tensor experiment](https://github.com/leanprover-community/liquid/).

* [blueprint](https://mmasdeu.github.io/brouwerfixedpoint/)
* [dependency graph](https://mmasdeu.github.io/brouwerfixedpoint/dep_graph.html)

## Dependencies

If you simply want to produce the `pdf` version of the blueprint, you don't
need anything beyond your usual TeX installation.

In order to build the `html` version you need 
[plasTeX](https://github.com/plastex/plastex/) and its 
[blueprint plugin](https://github.com/PatrickMassot/leanblueprint). 
You first need to make sure you have a decent python (at least 3.6). 
Then you can install:

```bash
pip install git+https://github.com/plastex/plastex.git
pip install git+https://github.com/PatrickMassot/leanblueprint.git
pip install invoke
```

Also installing `pdf2svg`, `pdfcrop`, and `xelatex` may be useful:

```bash
apt install pdf2svg
apt install texlive-extra-utils
apt install texlive-xetex
```

## Building

The source for the blueprint is in `doc`. 
If you only want to build it as a `pdf` file then you can simply run 
`xelatex blueprint.tex` or `lualatex blueprint.tex` (or even `pdflatex blueprint.tex`
if you are stuck in the past).

More complicated goals are easier to handle using [python invoke](https://www.pyinvoke.org/).
You can run `inv -l` to see the available actions. In particular `inv web` will build the website
and `inv serve` will serve it locally on port 8000.

Note that the dependency graph using graph-viz won't work if you simply open `web/dep_graph.html` in 
a browser because of browser paranoia. It has to be accessed through a web server. 

## Authoring

The main TeX file to edit is `content.tex`. It is a normal TeX file except that
each definition and statement must have a `\label` and there are four special LaTeX macros:
* `\lean{name}` indicates the fully namespaced Lean declaration that formalizes
  the current definition or statement.
* `\leanok` means the current definition, statement or proof has been fully formalized (in particular
  a lemma can have `\leanok` in its statement without having it in its proof environment.
* `\uses{refs}` where `refs` is a comma-separated list of LaTeX label can be
  put inside a definition, statement or proof environment. It means each of
  those labels is used by the current environment. This is what creates edges
  in the dependency graph. This mechanism is completely independent from
  `\ref`. With `leanok` this is the most important command to organize work.
  Note that `\uses` in proofs don't need to repeat those in the statement.
* `\proves{label}` can be put in a `proof` environment to indicate which
  statement is proved if this is not obvious (ie it is not proving the
  preceding statement).
