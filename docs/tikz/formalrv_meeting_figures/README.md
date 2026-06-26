# FormalRV meeting TikZ figures

Import setup:

```tex
\input{docs/tikz/formalrv_meeting_figures/formalrv_figures_preamble.tex}
```

Then import a figure body:

```tex
\begin{figure*}
  \centering
  \resizebox{\textwidth}{!}{%
    \input{docs/tikz/formalrv_meeting_figures/fig1_abstract_gap.tikz}}
  \caption{...}
\end{figure*}
```

Figure plan:

1. `fig1_abstract_gap.tikz` contrasts gadget-only scaling with FormalRV's semantic-plus-system path.
2. `fig2_formalrv_framework.tikz` explains the novelty: Lean contracts plus FT-VM finite-service modeling.
3. `fig3_vm_pipeline_no_hardware.tikz` shows the Lean theorem, verified layer workflow, and an aligned 2-bit Cuccaro example trace down to checked system calls.
4. `fig4_hardware_mapping.tikz` maps the same system calls onto neutral-atom and planar/superconducting backends.
5. `fig5_meeting_data_plot.tikz` gives two compact meeting plots from current repo facts.

Compile the preview:

```bash
python C:/Users/yezhu/.codex/plugins/cache/openai-bundled/latex/0.2.2/scripts/compile_latex.py C:/Users/yezhu/Documents/FormalRV/docs/tikz/formalrv_meeting_figures/preview_all.tex
```
