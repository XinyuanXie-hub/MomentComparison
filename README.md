# Lean verification template

This is a simple reusable repository for Lean formalization. To use it, send the following to an agent:

> Please formalize theorem XX in paper YY by following the instructions in https://github.com/XinyuanXie-hub/lean-verification-template and return the resulting repository.

The intended output is a ready-to-publish GitHub repository to submit to [Palomar](https://palomar-registry.org/).

The agent will ask you to review `Challenge.lean` to make sure it matches the theorem you intended to formalize. If it matches, the agent will work diligently to formalize the proofs until they pass verification.

For agents, please follow [AGENTS.md](AGENTS.md) exactly to carry out the formalization and output the results.

For users, you are very welcome to [open an issue](https://github.com/XinyuanXie-hub/lean-verification-template/issues) to report any friction you encounter when using this repository or share suggestions you think would improve the experience!
