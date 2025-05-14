# Constraint Satisfaction Planning with LLM Coding and Inference-Time Scaling

## Overview

Real-life textual planning tasks such as meeting scheduling have posed much challenge to LLMs especially when the complexity is high. While previous work primarily studied auto-regressive generation of plans with closed-source models, we systematically survey and show the strength of both closed- and open-source models in generating programs, which are executed to output the plan. We consider not only standard Python code, but also the code to a constraint satisfaction problem solver that conforms to syntactically scaffolding of a family of planning tasks. Further, we show the latest reasoning models performs significantly better when generating both plans and programs. Finally, we provide a detailed analysis on the programs and reasoning tokens to understand models' failure.

![Constraint Satisfaction Planning](images/thumbnail.png)

We evaluate on the [Natrual Plan](https://github.com/google-deepmind/natural-plan) benchmark on three tasks: calendar scheduling, trip planning, and meeting planning. We use LLMs with three types of output: plans, Python code, and [Z3](https://github.com/Z3Prover/z3) code. 

## Data

The downsampled 100-example-per-task datasets are in [data/](data/)`*_100.json` created via [source/downsample_data.py](source/downsample_data.py).

## Evaluation

### Plan

### Python


### Z3 
For Z3 code generation, go to [source/](source/) and run
> python generate_smt_input.py --model MODEL --data DATA

where `MODEL` is a model name supported HuggingFace, OpenAI API, or DeepSeek APi; `DATA` is one of *calendar*, *trip*, *meeting*, or all. 

Next, execute the generated code with
> python execute_smt.py --model MODEL --data DATA

and evaluate the output plan with
> python evaluate_smt_output.py --model MODEL --data DATA

This creates corresponding files and a readable report in [output/SMT/](output/SMT/)`MODEL/TASK/report.json`. 