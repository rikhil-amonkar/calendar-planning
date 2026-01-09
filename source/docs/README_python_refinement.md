{\rtf1\ansi\ansicpg1252\cocoartf2759
\cocoatextscaling0\cocoaplatform0{\fonttbl\f0\fnil\fcharset0 Menlo-Regular;\f1\fnil\fcharset0 Menlo-Italic;}
{\colortbl;\red255\green255\blue255;\red0\green0\blue0;\red0\green0\blue0;\red207\green214\blue228;
\red205\green204\blue213;\red218\green124\blue212;\red245\green188\blue80;\red255\green255\blue255;\red233\green160\blue109;
\red229\green189\blue123;}
{\*\expandedcolortbl;;\cssrgb\c0\c0\c0;\csgray\c0\c0;\cssrgb\c84706\c87059\c91373;
\cssrgb\c83922\c83922\c86667;\cssrgb\c89020\c58039\c86275;\cssrgb\c97255\c78039\c38431;\cssrgb\c100000\c100000\c100000;\cssrgb\c93725\c69020\c50196;
\cssrgb\c92157\c78431\c55294;}
\margl1440\margr1440\vieww11520\viewh8400\viewkind0
\deftab720
\pard\pardeftab720\partightenfactor0

\f0\fs24 \cf2 \cb3 \expnd0\expndtw0\kerning0
Iterative Python Refinement Pipeline\

This document describes the parallel processing pipeline implemented in iterative_python_refinement_parallel.py for solving scheduling tasks using iterative refinement with Python code generation via LLMs.\

Pipeline Overview\

The program processes calendar scheduling, meeting planning, and trip planning tasks through multiple refinement passes. Each pass generates Python code using a language model, executes it, evaluates the solution, and provides feedback for improvement. The process continues until a valid solution is found or the maximum number of passes is reached.\

Key Features\

1. Multi-task Support: Handles three distinct scheduling tasks:
   - Calendar scheduling (find meeting times)
   - Meeting planning (optimize multi-person schedules)
   - Trip planning (create travel itineraries)
   
2. Parallel Processing: Configurable concurrency (--max_concurrent) for efficient processing
3. Rate Limiting: API request throttling (--rate_limit) to prevent service overload
4. Iterative Refinement: Up to 5 passes (configurable) with constraint feedback
5. Comprehensive Evaluation: Exact matching and constraint satisfaction checks
6. Detailed Logging: Complete execution traces and error reporting
7. State Persistence: Tracks progress across runs\

Pipeline Steps\

1. Initialization\
Input:\
- Task type: "calendar", "meeting", "trip", or "all"\
- Model name(s): "DeepSeek-R1", "DeepSeek-V3", or HuggingFace model paths\
- Processing parameters: max_passes, max_concurrent, rate_limit\

Output:\
- Loaded task examples from JSON files in data/ directory\
- Initialized model connections (DeepSeek, OpenAI, or HuggingFace)\
- Created output directory structure\

2. Parallel Processing Setup\
Input:\
- List of task examples\
- Number of workers (--max_concurrent)\
- Rate limiting parameters (--rate_limit)\

Output:\
- Configured semaphore for parallel execution\
- Rate limiter for API calls\
- Worker pool for parallel processing\

3. Example Processing (per example)\
For each example, the following steps are executed in sequence until success or max_passes:\

3.1. Prompt Construction\
Input:\
- Task description from example\
- Task type-specific instructions (prefix/suffix)\
- Previous feedback (for refinement passes)\

Output:\
- Formatted prompt for the language model\
Example prompts for different tasks:\

# Calendar Task Prompt\
You are an expert at scheduling meetings. Your task is to find a suitable time for a meeting based on the participants' schedules and constraints. In this case:\

[Task description from example]\

Generate a fully working Python script with code that calculates a proposed time and outputs it in the format HH:MM:HH:MM.\
The script should also output the day of the week (e.g., Monday, Tuesday).\
The script should be clean, well-formatted, and enclosed within ```python and ```.\
The output of the generated code must include both the time range (like {14:30:15:30}) and the day of the week.\
Provide the response with only code.\

# Meeting Task Prompt\
You are an expert computational meeting planner. Your task is to write a Python program that algorithmically calculates the optimal meeting schedule based on the participants' constraints.\
The program must actually compute the plan using the given parameters, not just print a pre-determined answer.\
Input parameters:\

[Task description from example]\

Generate a complete, self-contained Python program that:\
1. Takes the above meeting constraints as input variables\
2. Computes the optimal meeting schedule using logical rules and calculations\
3. Outputs the result as a JSON-formatted dictionary with the following structure:\
{\n\
'  "itinerary": [\n'\
'    {"action": "meet", "location": "Location Name", "person": "Person Name", "start_time": "H:MM", "end_time": "H:MM"},\n'\
'    {"action": "meet", "location": "Location Name", "person": "Person Name", "start_time": "H:MM", "end_time": "H:MM"}\n'\
  ]\n\
}\
Rules for the program:\
- Times should be in 24-hour format like '9:00' or '13:30' (no leading zero)\
- The schedule must account for all travel times and constraints\
- The program must actually compute the schedule, not just print a static answer\
Output only the complete Python code with no additional text or explanation.\
The code must run independently and output valid JSON when executed.\

# Trip Task Prompt\
You are an expert computational trip planner.\
Your task is to write a Python program that algorithmically calculates the optimal itinerary based on the participants' constraints.\
The program must actually compute the plan using the given parameters, not just print a predetermined answer.\

[Task description from example]\

Generate a complete, self-contained Python program that:\
1. Takes the above trip constraints as input variables\
2. Computes the optimal itinerary using logical rules and calculations\
3. Outputs the result as a JSON-formatted dictionary with an 'itinerary' key containing a list of day-place mappings.\
Example structure of output from running code: {\"itinerary\": [{\"day_range\": \"Day 1-5\", \"place\": \"Helsinki\"}, {\"day_range\": \"Day 5-9\", \"place\": \"Barcelona\"}, {\"day_range\": \"Day 9-14\", \"place\": \"Florence\"}]}\
Note that the JSON structure should be what the Python program outputs, not just a string representation.\
4. Note that if one flies from city A to city B on day X, then they are in both cities A and B on day X, which contributes to the total number of days in each city.\
The program must include:\
- Actual calculations to determine durations and transitions\
Output only the complete Python code with no additional text or explanation.\
The code must run independently and output valid JSON when executed.\

3.2. Model Inference\
Input:\
- Constructed prompt\
- Model parameters (temperature, max tokens, etc.)\

Models Used:\
- Primary LLM (specified by --model argument):\
  - DeepSeek models (R1, V3)\
  - OpenAI models\
  - HuggingFace models\

Output:\
- Model response containing:\
  - Natural language explanation (if any)\
  - Python code solution\
  - Solution in specified format\

3.3. Code Extraction\
Input:\
- Model response text\

Process:\
- Extracts code between ```python and ``` markers\
- Falls back to heuristic code detection if delimiters not found\

Output:\
- Clean Python code ready for execution\

3.4. Code Execution\
Input:\
- Generated Python code\
- Task-specific constraints\

Process:\
- Saves code to temporary file\
- Executes via subprocess\
- Captures stdout/stderr\

Output:\
- Execution result containing:\
  - has_execution_error: Boolean\
  - execution_output: Output or error message\
  - execution_time: Duration in seconds\

3.5. Solution Evaluation\
Input:\
- Execution output\
- Task-specific constraints\
- Gold standard solution\

Evaluation Process:\
1. Output parsing into structured format\
2. Constraint satisfaction checking\
3. Exact match comparison with golden solution\

Output:\
- Evaluation result containing:\
  - pred: Extracted prediction\
  - gold: Gold standard solution\
  - is_exact_match: Boolean\
  - constraints_satisfied: Boolean\
  - violated_constraints: List of issues\
  - status: "Correct", "Error", or "Wrong plan"\

3.6. Feedback Generation\
Input:\
- Evaluation results\
- Execution output\
- Violated constraints\

Output:\
- Enhanced prompt for next iteration containing:\
  - For execution errors: Full error trace and problematic code\
  - For constraint violations: Specific feedback on what constraints were violated\
  - Previous code for reference\

3.7. Iteration Control\
The process continues until one of:\
- Correct solution found (constraints satisfied + exact match)\
- Maximum passes reached (default: 5)\
- Unrecoverable error occurs\

4. Results Collection\
Output directory structure:\
output/\
\uc0\u9500 \u9472 \u9472 Python/\
\uc0\u9474    \u9500 \u9472 \u9472 {model_name}/\
\uc0\u9474    \u9474    \u9500 \u9472 \u9472 {task_type}/\
\uc0\u9474    \u9474    \u9474    \u9500 \u9472 \u9472 n_pass/\
\uc0\u9474    \u9474    \u9474    \u9474    \u9500 \u9472 \u9472 {example_id}/\
\uc0\u9474    \u9474    \u9474    \u9474    \u9474    \u9500 \u9472 \u9472 1_pass/\
\uc0\u9474    \u9474    \u9474    \u9474    \u9474    \u9474    \u9500 \u9472 \u9472 conversation.json\
\uc0\u9474    \u9474    \u9474    \u9474    \u9474    \u9474    \u9500 \u9472 \u9472 solution.py\
\uc0\u9474    \u9474    \u9474    \u9474    \u9474    \u9474    \u9500 \u9472 \u9472 output.out\
\uc0\u9474    \u9474    \u9474    \u9474    \u9474    \u9474    \u9492 \u9472 \u9472 evaluation.json\
\uc0\u9474    \u9474    \u9474    \u9474    \u9474    \u9500 \u9472 \u9472 2_pass/\
\uc0\u9474    \u9474    \u9474    \u9474    \u9474    \u9492 \u9472 \u9472 ...\

5. Analysis and Reporting\
Generated Files:\
- Per-pass execution details\
- Comprehensive timing metrics\
- Final statistics including:\
  - Completion rates\
  - Exact match percentages\
  - Average passes per example\

Running the Pipeline\

Basic Usage:\
\f1\i # Run calendar task with default settings
\f0\i0 python iterative_python_refinement_parallel.py --task calendar --model DeepSeek-R1\

\f1\i # Run all tasks with multiple models
\f0\i0 python iterative_python_refinement_parallel.py --task all --model DeepSeek-R1 gpt-4o-mini\

\f1\i # Custom number of passes and concurrency
\f0\i0 python iterative_python_refinement_parallel.py --task meeting --model DeepSeek-R1 --max_passes 3 --max_concurrent 10\

Advanced Options:\
\f1\i # Process specific examples only
\f0\i0 python iterative_python_refinement_parallel.py --task calendar --examples "25,35,42"\

\f1\i # Custom rate limiting
\f0\i0 python iterative_python_refinement_parallel.py --task trip --rate_limit 5\

\f1\i # Force fresh run (ignore existing results)
\f0\i0 python iterative_python_refinement_parallel.py --task all --fresh\

Command Line Arguments:\
- --task: Task type ("calendar", "meeting", "trip", or "all")\
- --model: One or more model names\
- --max_passes: Max refinement attempts (default: 5)\
- --max_concurrent: Parallel examples (default: 5)\
- --rate_limit: API requests per second\
- --start/--end: Example range\
- --examples: Specific example numbers\
- --fresh: Ignore previous results\

Key Components\

1. SchedulingProgram Class:\
- Main controller coordinating all pipeline steps\
- Handles task-specific configurations\
- Manages parallel execution\

2. RateLimiter Class:\
- Ensures API calls stay within rate limits\
- Configurable requests-per-second\

3. EvaluationState Class:\
- Tracks progress across runs\
- Persists to JSON file\
- Provides completion statistics\

4. Task-Specific Handlers:\
- Prompt templates (prefix/suffix)\
- Output parsers\
- Constraint evaluators\
- Feedback formatters\

Implementation Notes\

1. The pipeline uses asyncio for efficient parallel processing\
2. All generated artifacts are saved for reproducibility\
3. The state tracking allows resuming interrupted runs\
4. Comprehensive error handling throughout\
5. Detailed timing metrics for performance analysis\
6. Supports both API-based and local models\
7. Configurable through command line arguments\
}
