# Constraint Satisfaction Planning with LLM Coding and Inference-Time Scaling

## Overview

Real-life textual planning tasks such as meeting scheduling have posed much challenge to LLMs especially when the complexity is high. While previous work primarily studied auto-regressive generation of plans with closed-source models, we systematically survey and show the strength of both closed- and open-source models in generating programs, which are executed to output the plan. We consider not only standard Python code, but also the code to a constraint satisfaction problem solver that conforms to syntactically scaffolding of a family of planning tasks. Further, we show the latest reasoning models performs significantly better when generating both plans and programs. Finally, we provide a detailed analysis on the programs and reasoning tokens to understand models' failure.

![Constraint Satisfaction Planning](images/thumbnail.png)

We evaluate on the [Natural Plan](https://github.com/google-deepmind/natural-plan) benchmark on three tasks: calendar scheduling, trip planning, and meeting planning. We use LLMs with three types of output: plans, Python code, and [Z3](https://github.com/Z3Prover/z3) code. 

## Data

The downsampled 100-example-per-task datasets are in [data/](data/)`*_100.json` created via [source/downsample_data.py](source/downsample_data.py).

## Evaluation

### Plan
For plan generation on HuggingFace models, go to [source/](source/) and run
> python force_json_[TASK]_text.py --model MODEL

where `TASK` is one of *calendar*, *trip*, *meeting* tasks; `MODEL` is a model name supported HuggingFace

For plan generation on OpenAI models, go to [source/](source/) and run
> python openai_force_json_[TASK]_text.py --model MODEL

where `TASK` is one of *calendar*, *trip*, *meeting* tasks; `MODEL` is a model name supported OpenAI API

For plan generation with reasoning on DeepSeek models, go to [source/](source/) and run
> python deepseek_opai_[TASK]_text_reason.py --model MODEL

where `TASK` is one of *calendar*, *trip*, *meeting* tasks; `MODEL` is a model name supported DeepSeek API

Now evaluate the output plan with
> python evaluate_by_constraint.py --task TASK --model MODEL --output OUTPUT

where `TASK` is one of *calendar*, *trip*, *meeting*, or all.; `MODEL` is a model name supported HuggingFace, OpenAI API, or DeepSeek API; `OUTPUT` is either *plan* or *python*

This creates corresponding files and a readable report in [output/Plan/](output/Plan/)`MODEL/TASK/report.json`. 

### Python
For Python code generation, go to [source/](source/) and run
> python [TASK]_plan_code_gen.py --model MODEL

where `TASK` is one of *calendar*, *trip*, *meeting* tasks; `MODEL` is a model name supported HuggingFace

For Python code generation on OpenAI models, go to [source/](source/) and run
> python openai_[TASK]_plan_code_gen.py --model MODEL

where `TASK` is one of *calendar*, *trip*, *meeting* tasks; `MODEL` is a model name supported OpenAI API

For Python code generation with reasoning on DeepSeek models, go to [source/](source/) and run
> python deepseek_opai_[TASK]_code_reason.py --model MODEL

where `TASK` is one of *calendar*, *trip*, *meeting* tasks; `MODEL` is a model name supported DeepSeek API

Now evaluate the output plan from the Python generated outputs with
> python evaluate_by_constraint.py --task TASK --model MODEL --output OUTPUT

where `TASK` is one of *calendar*, *trip*, *meeting*, or all.; `MODEL` is a model name supported HuggingFace, OpenAI API, or DeepSeek API; `OUTPUT` is either *plan* or *python*

This creates corresponding files and a readable report in [output/Python/](output/Python/)`MODEL/TASK/report.json`. 

### Z3 
For Z3 code generation, go to [source/](source/) and run
> python generate_smt_input.py --model MODEL --data DATA

where `MODEL` is a model name supported HuggingFace, OpenAI API, or DeepSeek API; `DATA` is one of *calendar*, *trip*, *meeting*, or all. 

Execute the generated code:
> python execute_smt.py --model MODEL --data DATA

Convert the output into a unified format:
> python convert_smt_output_format.py --model MODEL --data DATA

Evaluate against constraints:
> python evaluate_by_constraint.py --output z3 --model MODEL --data DATA

This creates corresponding files and a readable report in [output/SMT/](output/SMT/)`MODEL/TASK/report.json`. 
