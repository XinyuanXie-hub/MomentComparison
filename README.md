# Lean verification template

This is a simple reusable repository for Lean formalization.

To use it, just copy and paste the following sentence into a chat with your agent, replacing `XX` and `YY` with the specific theorems you want to formalize and the papers they come from.

> Please formalize theorem XX in paper YY using https://github.com/XinyuanXie-hub/lean-verification-template and output as instructed there.

The intended output is a ready-to-publish GitHub repository to submit to [Palomar](https://palomar-registry.org/). You need to make sure that `Challenge.lean` states the theorem you really want to formalize. More specific details are available in the [system specification in AGENTS.md](AGENTS.md#system-specification).

## Intended interactions

The agent will prompt the user to give the name of the repository, then to review `Challenge.lean`, if approved, the agent will keep working until it passes the comparator check.

For agents, please follow [AGENTS.md](AGENTS.md) exactly to carry out the formalization and output the results.

For users, you are welcome to [open an issue](https://github.com/XinyuanXie-hub/lean-verification-template/issues) if you run into any friction or have any suggestions to improve the experience.
