# Coq Template:

This is the `ku-sldg` template for creating new Coq projects and plugins.
In particular, we can use this for ocaml style plugins (via `ocaml_plugin` and `dune` options) or just plain Coq libraries.

## Pre-Reqs

- Install [mustache](https://mustache.github.io/) (in particular linux can use `ruby-mustache` package)

## To create a new Coq project:

1. Create a new repository (in GitHub) based off this repo
1. Edit the `meta.yml` file. It should be relatively well documented, but reach out to [Will](https://github.com/Durbatuluk1701) if you have questions
1. Run `make meta`

## Notes:

- Anytime your goals for the project change, make sure you modify the `meta.yml` file and re-run `make meta`
- Anytime this generates infrastructure that is not useful, or needs to be modified, please open an issue in this repo and ping @Durbatuluk1701
