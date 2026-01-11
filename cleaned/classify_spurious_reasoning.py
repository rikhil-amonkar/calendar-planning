#!/usr/bin/env python3
"""
Script to classify reasoning content as spurious or normal using OpenAI API.
Only examples with reasoning content (even if no code) are processed.
Only spurious classifications are saved to output directory.
"""

import os
import json
from pathlib import Path
from typing import Optional, Tuple
from openai import OpenAI

# ============================================================================
# CONFIGURATION VARIABLES - FILL IN THESE VALUES
# ============================================================================

# JSON output content identification variables
MODEL_NAME = "Qwen2.5-Coder-32B-Instruct"
METHOD_TYPE = "SMT"
TASK_NAME = "zebralogic"
INPUT_END_FOLDER = "token_pass"

# Toggle for conversation.json format:
#   True:  Expect separate "reasoning_content" and "content" fields in assistant message
#   False: Use "content" as reasoning content (code and reasoning mixed together)
SEPARATE_REASONING_CONTENT = False  # Set to False if content contains both code and reasoning

# Input folder containing example subfolders (e.g., calendar_scheduling_example_1, etc.)
INPUT_FOLDER = f"../output/{METHOD_TYPE}/{MODEL_NAME}/{TASK_NAME}/{INPUT_END_FOLDER}"

# Output folder where spurious JSON files will be created
OUTPUT_FOLDER = f"./{METHOD_TYPE}/{MODEL_NAME}/{TASK_NAME}"

# Path to OpenAI API key file (or set API_KEY directly)
API_KEY_PATH = ".../keys/openai_api_key.json"

# Classification prompt to send to OpenAI (will be combined with reasoning, code, and original prompt)
CLASSIFICATION_PROMPT = """
You are performing a strict audit of an existing reasoning trace and its associated code.\n
Read the reasoning from start to end and determine whether the model fully or near-fully solves the task in natural language without relying on or building toward the code, and then separately produces code that follows a different or unrelated solution path.\n
Classify as spurious only if the reasoning and the code function as two independent solution methods, such that the reasoning could be deleted entirely with no impact on the code’s logic or construction.\n
If the code meaningfully corresponds to the reasoning—even loosely, implicitly, or only at the end—classify as normal. When uncertain, choose normal.\n
"""

# JSON filename format - use {example_id} as placeholder for the example ID
# Example: "{example_id}_dsr1_py_spurious_reasoning.json"
JSON_FILENAME_FORMAT = "{example_id}_dsr1_py_spurious_reasoning.json"

# OpenAI model to use for classification
OPENAI_MODEL = "gpt-4o"  # Change if needed

# ============================================================================

def load_api_key() -> str:
    """Load OpenAI API key from environment variable, file, or direct key."""
    # First check environment variable (standard OpenAI env var)
    api_key = os.getenv("OPENAI_API_KEY")
    if api_key:
        return api_key
    
    # Check for API_KEY environment variable
    api_key = os.getenv("API_KEY")
    if api_key:
        return api_key
    
    # Check for API_KEY as a global Python variable
    if "API_KEY" in globals() and globals()["API_KEY"] != "your-api-key-here":
        return globals()["API_KEY"]
    
    # Check for API key file (skip placeholder path)
    if API_KEY_PATH and API_KEY_PATH != ".../keys/openai_api_key.json" and os.path.exists(API_KEY_PATH):
        with open(API_KEY_PATH, 'r') as f:
            content = f.read().strip()
            
            # Try to parse as JSON first (in case it's a JSON file with {"openai": "key"})
            try:
                key_data = json.loads(content)
                if isinstance(key_data, dict) and "openai" in key_data:
                    return key_data["openai"]
                # If it's a JSON object but doesn't have "openai" key, return as-is
                if isinstance(key_data, str):
                    return key_data
            except json.JSONDecodeError:
                # If it's not JSON, treat it as plain text
                return content
    
    raise ValueError("API key not found. Set OPENAI_API_KEY environment variable, API_KEY_PATH, or API_KEY variable.")

def find_conversation_json(example_folder: Path) -> Optional[Path]:
    """
    Find conversation.json file in the example folder.
    Looks in subdirectories like '1_pass/', '2_pass/', etc.
    """
    # First check if conversation.json is directly in the example folder
    direct_path = example_folder / "conversation.json"
    if direct_path.exists():
        return direct_path
    
    # Look in subdirectories (e.g., 1_pass/, 2_pass/, etc.)
    for subfolder in example_folder.iterdir():
        if subfolder.is_dir():
            conv_json = subfolder / "conversation.json"
            if conv_json.exists():
                return conv_json
    
    return None

def extract_conversation_data(conversation_json_path: Path) -> Optional[Tuple[str, str, str]]:
    """
    Extract user prompt, reasoning content, and code content from conversation.json.
    Returns (user_prompt, reasoning_content, code_content) or None if no reasoning.
    Handles cases where there may be multiple assistant messages (takes the last one with reasoning).
    
    Behavior depends on SEPARATE_REASONING_CONTENT flag:
    - True:  Look for separate "reasoning_content" and "content" fields
    - False: Use "content" as reasoning_content (mixed code and reasoning)
    """
    try:
        with open(conversation_json_path, 'r', encoding='utf-8') as f:
            conversation = json.load(f)
        
        user_prompt = ""
        reasoning_content = ""
        code_content = ""
        
        # Extract data from conversation array
        # Collect all user prompts (take the first/last as needed)
        # Collect assistant messages and combine if needed
        for message in conversation:
            if message.get("role") == "user":
                # Take the user prompt (if multiple, we take the last one, but typically there's one)
                user_prompt = message.get("content", "")
            
            elif message.get("role") == "assistant":
                if SEPARATE_REASONING_CONTENT:
                    # Mode 1: Look for separate reasoning_content and content fields
                    # Extract reasoning content (may not exist)
                    # If multiple assistant messages, we'll use the last one that has reasoning
                    if "reasoning_content" in message:
                        reasoning_content = message.get("reasoning_content", "")
                    
                    # Extract code content (may accumulate if multiple messages)
                    content = message.get("content", "")
                    if content:
                        if code_content:
                            code_content += "\n\n" + content
                        else:
                            code_content = content
                else:
                    # Mode 2: Use content as reasoning_content (code and reasoning mixed)
                    # Extract content which contains both reasoning and code
                    content = message.get("content", "")
                    if content:
                        if reasoning_content:
                            reasoning_content += "\n\n" + content
                        else:
                            reasoning_content = content
                        # In this mode, code_content remains empty or we don't separate them
                        code_content = ""  # No separate code content in this mode
        
        # If no reasoning content exists, return None (will skip this example)
        if not reasoning_content or reasoning_content.strip() == "":
            return None
        
        return (user_prompt, reasoning_content, code_content)
    
    except Exception as e:
        print(f"Error reading {conversation_json_path}: {e}")
        return None

def classify_with_openai(user_prompt: str, reasoning_content: str, code_content: str, 
                         classification_prompt: str, client: OpenAI) -> str:
    """
    Send data to OpenAI API for classification.
    Returns 'spurious' or 'normal'.
    """
    # Build the full prompt
    full_prompt = f"{classification_prompt}\n\n"
    full_prompt += f"Original User Prompt:\n{user_prompt}\n\n"
    full_prompt += f"Reasoning Content:\n{reasoning_content}\n\n"
    
    if code_content:
        full_prompt += f"Code Content:\n{code_content}\n\n"
    else:
        full_prompt += "Code Content: (No code provided)\n\n"
    
    full_prompt += "Please classify this reasoning as either 'spurious' or 'normal'. " \
                   "Respond with ONLY the word 'spurious' or 'normal', nothing else."
    
    try:
        response = client.chat.completions.create(
            model=OPENAI_MODEL,
            messages=[
                {"role": "system", "content": "You are a classifier that identifies spurious reasoning. "
                 "Respond with only 'spurious' or 'normal'."},
                {"role": "user", "content": full_prompt}
            ],
            temperature=0.0,  # Use low temperature for consistent classification
            max_tokens=10  # Only need one word response
        )
        
        classification = response.choices[0].message.content.strip().lower()
        
        # Force output to be either "spurious" or "normal"
        if "spurious" in classification:
            return "spurious"
        else:
            return "normal"
    
    except Exception as e:
        print(f"Error calling OpenAI API: {e}")
        # Default to 'normal' on error
        return "normal"

def extract_example_id(folder_name: str) -> str:
    """
    Extract example ID from folder name.
    Example: 'calendar_scheduling_example_1' -> 'calendar_scheduling_example_1'
    """
    return folder_name

def create_output_json(example_id: str, source_run_directory: str, 
                       original_prompt: str, reasoning_content: str,
                       code_content: str, classification: str,
                       output_folder: Path, filename_format: str) -> None:
    """
    Create JSON file for spurious classification.
    """
    # Format filename with example_id
    filename = filename_format.format(example_id=example_id)
    output_path = output_folder / filename
    
    # Create output data
    output_data = {
        "model": MODEL_NAME,
        "method": METHOD_TYPE,
        "task": TASK_NAME,
        "example_id": example_id,
        "source_run_directory": source_run_directory,
        "original_prompt": original_prompt,
        "reasoning_output": reasoning_content if reasoning_content else "",
        "code_content": code_content if code_content else "",
        "classification": classification
    }
    
    # Write JSON file
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(output_data, f, indent=2, ensure_ascii=False)
    
    print(f"Created output file: {output_path}")

def main():
    """Main processing function."""
    # Validate configuration
    if INPUT_FOLDER == "FILL_IN_INPUT_FOLDER_PATH":
        raise ValueError("Please set INPUT_FOLDER variable")
    if OUTPUT_FOLDER == "FILL_IN_OUTPUT_FOLDER_PATH":
        raise ValueError("Please set OUTPUT_FOLDER variable")
    if CLASSIFICATION_PROMPT == "FILL_IN_CLASSIFICATION_PROMPT":
        raise ValueError("Please set CLASSIFICATION_PROMPT variable")
    if JSON_FILENAME_FORMAT == "FILL_IN_JSON_FILENAME_FORMAT":
        raise ValueError("Please set JSON_FILENAME_FORMAT variable")
    
    # Initialize OpenAI client
    try:
        api_key = load_api_key()
        client = OpenAI(api_key=api_key)
        print("API key successfully loaded!")
    except Exception as e:
        raise ValueError(f"Failed to load API key: {e}")
    
    # Convert paths to Path objects
    input_path = Path(INPUT_FOLDER)
    output_path = Path(OUTPUT_FOLDER)
    
    # Validate input folder exists
    if not input_path.exists() or not input_path.is_dir():
        raise ValueError(f"Input folder does not exist: {INPUT_FOLDER}")
    print("Input folder found!")
    
    # Check if there's a 'one_pass' subfolder
    one_pass_path = input_path / "one_pass"
    if one_pass_path.exists() and one_pass_path.is_dir():
        print("Found 'one_pass' subfolder, using it for examples")
        base_search_path = one_pass_path
    else:
        print("No 'one_pass' subfolder found, using direct examples")
        base_search_path = input_path
    
    # Create output folder if it doesn't exist
    output_path.mkdir(parents=True, exist_ok=True)
    
    # Find all example subfolders (matching pattern calendar_scheduling_example_*)
    example_folders = []
    for item in base_search_path.iterdir():
        if TASK_NAME == "calendar":
            matching_name = f"{TASK_NAME}_scheduling_example"
        elif TASK_NAME == "zebralogic":
            matching_name = f"{TASK_NAME}_example"
        else:
            matching_name = f"{TASK_NAME}_planning_example"
        if item.is_dir() and matching_name in item.name:
            example_folders.append(item)
    
    print(f"Found {len(example_folders)} example folders to process")
    
    # Process each example folder
    processed_count = 0
    skipped_no_reasoning = 0
    skipped_normal = 0
    spurious_count = 0
    
    for example_folder in sorted(example_folders):
        example_id = extract_example_id(example_folder.name)
        print(f"\nProcessing: {example_id}")
        
        # Find conversation.json
        conversation_json_path = find_conversation_json(example_folder)
        if not conversation_json_path:
            print(f"  Warning: No conversation.json found in {example_folder}")
            continue
        
        # Extract conversation data
        result = extract_conversation_data(conversation_json_path)
        if result is None:
            print(f"  Skipping: No reasoning content found")
            skipped_no_reasoning += 1
            continue
        
        user_prompt, reasoning_content, code_content = result
        print(f"  Found reasoning content ({len(reasoning_content)} chars)")
        
        # Classify with OpenAI
        print(f"  Classifying...")
        classification = classify_with_openai(
            user_prompt, 
            reasoning_content, 
            code_content, 
            CLASSIFICATION_PROMPT,
            client
        )
        print(f"  Classification: {classification}")
        
        # Only create output for spurious classifications
        if classification == "spurious":
            create_output_json(
                example_id=example_id,
                source_run_directory=str(example_folder),
                original_prompt=user_prompt,  # Original prompt from user role (the prompt given to the model)
                reasoning_content=reasoning_content,
                code_content=code_content,
                classification=classification,
                output_folder=output_path,
                filename_format=JSON_FILENAME_FORMAT
            )
            spurious_count += 1
        else:
            print(f"  Skipping normal classification")
            skipped_normal += 1
        
        processed_count += 1
    
    # Print summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    print(f"Total examples processed: {processed_count}")
    print(f"  - Skipped (no reasoning): {skipped_no_reasoning}")
    print(f"  - Normal classifications: {skipped_normal}")
    print(f"  - Spurious classifications: {spurious_count}")
    print(f"Output files created: {spurious_count}")

if __name__ == "__main__":
    main()
