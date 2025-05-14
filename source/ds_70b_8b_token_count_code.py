import json
import tiktoken

def process_json_file(json_file_path):
    # Load the JSON data
    with open(json_file_path, 'r') as file:
        data = json.load(file)
    
    # Initialize token counting
    encoding = tiktoken.encoding_for_model("gpt-4")
    
    results = []
    total_tokens = 0
    example_count = 0
    
    # Process each example in the 0shot array
    for example in data["0shot"]:
        # Extract the ID and raw response
        example_id = example["count"]
        raw_response = example["raw_model_response"]
        
        # Find the </think> marker and extract the thinking text
        think_end = raw_response.find("</think>")
        if think_end == -1:
            continue  # skip if no thinking text found
            
        thinking_text = raw_response[:think_end].strip()
        
        # Count tokens
        tokens = encoding.encode(thinking_text)
        token_count = len(tokens)
        
        # Add to results
        results.append({
            "id": example_id,
            "token_count": token_count
        })
        
        # Update totals
        total_tokens += token_count
        example_count += 1
    
    # Calculate average
    average_tokens = total_tokens / example_count if example_count > 0 else 0
    
    # Generate output text
    output_lines = []
    for result in results:
        output_lines.append(f"{result['id']}: {result['token_count']} tokens")
    
    output_lines.append(f"\nAverage tokens per example: {average_tokens:.2f}")
    
    return "\n".join(output_lines)

# Example usage (you would replace this with your actual JSON file path)
json_file_path = "meeting_planning/100_random_0shot_code_outputs_new/DS-R1-DL-8B_code_meeting_results.json"
output_text = process_json_file(json_file_path)

# Save to a text file
with open("token_counts.txt", "w") as out_file:
    out_file.write(output_text)

print("Token counts saved to token_counts.txt")
