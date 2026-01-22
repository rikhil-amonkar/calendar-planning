#!/usr/bin/env python3
"""
Convert text-based itinerary outputs to structured JSON format (with iterations support).

This version handles results from code_generation_inference_iterations.py which includes
multiple iterations per problem. It converts all iterations and stores the final iteration
as the main result.

Output format:
{
  "itinerary": [
    {"action": "meet", "person": "<name>", "start_time": "HH:MM", "end_time": "HH:MM"}
  ]
}

Times are in 24-hour format (HH:MM).
"""

import json
import re
from pathlib import Path
from typing import Dict, List, Optional
import sys


def parse_time_to_24h(time_str: str) -> Optional[str]:
    """
    Convert various time formats to 24-hour HH:MM format.
    
    Handles:
    - "9:45PM" -> "21:45"
    - "9:45AM" -> "09:45"
    - "21:45" -> "21:45"
    - "9:45" (assumes 24-hour if no AM/PM)
    - "21:45PM" (invalid, but tries to parse as 21:45)
    
    Args:
        time_str: Time string in various formats
    
    Returns:
        Time in HH:MM format, or None if parsing fails
    """
    time_str = time_str.strip()
    
    # Try to match various patterns
    # Pattern 1: HH:MM AM/PM (12-hour format)
    match = re.search(r'(\d{1,2}):(\d{2})\s*(AM|PM)', time_str, re.IGNORECASE)
    if match:
        hour = int(match.group(1))
        minute = int(match.group(2))
        am_pm = match.group(3).upper()
        
        # Check if hour is already in 24-hour format (13-23)
        # If so, ignore the AM/PM (it's a formatting error like "21:45PM")
        if hour >= 13:
            # Already in 24-hour format, ignore AM/PM
            return f"{hour:02d}:{minute:02d}"
        
        # Convert 12-hour to 24-hour
        if am_pm == 'PM' and hour != 12:
            hour += 12
        elif am_pm == 'AM' and hour == 12:
            hour = 0
        
        return f"{hour:02d}:{minute:02d}"
    
    # Pattern 2: HH:MM (24-hour format, or mixed format like "21:45PM")
    match = re.search(r'(\d{1,2}):(\d{2})', time_str)
    if match:
        hour = int(match.group(1))
        minute = int(match.group(2))
        
        # Validate
        if 0 <= hour <= 23 and 0 <= minute <= 59:
            return f"{hour:02d}:{minute:02d}"
    
    return None


def extract_location_from_text(text: str, person: str) -> Optional[str]:
    """
    Try to extract the location where a person is met.
    Looks for travel patterns before the person's name.
    
    Args:
        text: Full itinerary text
        person: Person name to find location for
    
    Returns:
        Location string or None
    """
    # Look for "You travel to <location>" patterns before the person mention
    lines = text.split('\n')
    current_location = None
    
    for line in lines:
        # Track location from travel lines
        travel_match = re.search(r'[Yy]ou travel to ([A-Z][^\.]+?)(?:\sin\s|\sat\s|\.)', line)
        if travel_match:
            # Clean up location (remove "in X minutes" etc)
            loc = travel_match.group(1).strip()
            # Remove trailing "in ..." or "at ..."
            loc = re.sub(r'\s+in\s+\d+.*', '', loc)
            loc = re.sub(r'\s+at\s+\d+.*', '', loc)
            current_location = loc
        
        # Check if this line mentions meeting the person
        if f'meet {person}' in line.lower() or f'meet {person}' in line:
            return current_location
    
    return None


def extract_meetings_from_text(text: str) -> List[Dict[str, str]]:
    """
    Extract meeting information from text-based itinerary.
    
    Handles various formats:
    - "You meet Margaret for 45 minutes from 9:45PM to 10:30PM."
    - "You meet David for 120 minutes from 13:00 to 15:00."
    - "Meet David at 13:00 for 120 minutes"
    - "You meet Margaret for 45 minutes from 21:45PM to 22:30PM." (catches formatting errors)
    
    Args:
        text: Text containing itinerary
    
    Returns:
        List of meeting dictionaries with action, person, location, start_time, end_time
    """
    meetings = []
    
    # Pattern 1: "You meet <person> for X minutes from <time> to <time>"
    pattern1 = r'[Yy]ou meet ([A-Z][a-z]+).*?from\s+([0-9:]+\s*(?:AM|PM)?)\s+to\s+([0-9:]+\s*(?:AM|PM)?)'
    matches1 = re.finditer(pattern1, text, re.IGNORECASE)
    
    for match in matches1:
        person = match.group(1)
        start_time = parse_time_to_24h(match.group(2))
        end_time = parse_time_to_24h(match.group(3))
        location = extract_location_from_text(text, person)
        
        if start_time and end_time:
            meetings.append({
                "action": "meet",
                "person": person,
                "location": location,
                "start_time": start_time,
                "end_time": end_time
            })
    
    # Pattern 2: "Meet <person> for X minutes from <time> to <time>"
    pattern2 = r'[Mm]eet ([A-Z][a-z]+).*?from\s+([0-9:]+\s*(?:AM|PM)?)\s+to\s+([0-9:]+\s*(?:AM|PM)?)'
    matches2 = re.finditer(pattern2, text, re.IGNORECASE)
    
    for match in matches2:
        person = match.group(1)
        start_time = parse_time_to_24h(match.group(2))
        end_time = parse_time_to_24h(match.group(3))
        location = extract_location_from_text(text, person)
        
        # Skip if already added (from pattern1)
        if start_time and end_time:
            meeting = {
                "action": "meet",
                "person": person,
                "location": location,
                "start_time": start_time,
                "end_time": end_time
            }
            if meeting not in meetings:
                meetings.append(meeting)
    
    # Pattern 3: "Meet <person> at <time> for X minutes"
    pattern3 = r'[Mm]eet ([A-Z][a-z]+) at ([0-9:]+\s*(?:AM|PM)?)'
    matches3 = re.finditer(pattern3, text, re.IGNORECASE)
    
    for match in matches3:
        person = match.group(1)
        start_time = parse_time_to_24h(match.group(2))
        location = extract_location_from_text(text, person)
        
        if start_time:
            # Try to find duration
            duration_match = re.search(r'for (\d+) minutes', text[match.start():match.end()+50])
            if duration_match:
                duration = int(duration_match.group(1))
                # Calculate end time
                start_hour, start_min = map(int, start_time.split(':'))
                total_minutes = start_hour * 60 + start_min + duration
                end_hour = (total_minutes // 60) % 24
                end_min = total_minutes % 60
                end_time = f"{end_hour:02d}:{end_min:02d}"
                
                meeting = {
                    "action": "meet",
                    "person": person,
                    "location": location,
                    "start_time": start_time,
                    "end_time": end_time
                }
                if meeting not in meetings:
                    meetings.append(meeting)
    
    return meetings


def convert_result_to_structured(result: Dict) -> Dict:
    """
    Convert a single result entry to structured format.
    
    Args:
        result: Result dictionary with 'output' field
    
    Returns:
        Structured output with 'itinerary' key
    """
    output_text = result.get('output', '')
    
    if not output_text or output_text.startswith('Traceback') or 'error' in output_text.lower()[:50]:
        # Execution failed or error
        return {"itinerary": []}
    
    meetings = extract_meetings_from_text(output_text)
    
    return {"itinerary": meetings}


def process_results_file(input_file: str, output_file: Optional[str] = None) -> None:
    """
    Process a results JSON file with iterations and convert all outputs to structured format.
    
    Args:
        input_file: Path to input JSON file (from code_generation_inference_iterations.py)
        output_file: Path to output JSON file (optional)
    """
    input_path = Path(input_file)
    
    if not input_path.exists():
        print(f"Error: File not found: {input_file}")
        sys.exit(1)
    
    # Load results
    with open(input_path, 'r') as f:
        results = json.load(f)
    
    print(f"✓ Loaded {len(results)} results from {input_file}")
    
    # Convert each result
    structured_results = []
    for result in results:
        # Check if this result has iterations
        iterations = result.get('iterations', [])
        num_iterations = result.get('num_iterations', 0)
        
        if iterations and num_iterations > 0:
            # Process each iteration
            structured_iterations = []
            
            for iter_data in iterations:
                iter_output = iter_data.get('output', '')
                iter_exec_success = iter_data.get('execution_success', False)
                iter_has_error = iter_data.get('has_code_error', False)
                iter_has_no_plan = iter_data.get('has_no_plan', False)
                
                # Convert this iteration's output to structured format
                iter_structured = convert_result_to_structured({
                    'output': iter_output,
                    'execution_success': iter_exec_success
                })
                
                structured_iterations.append({
                    'iteration': iter_data.get('iteration'),
                    'execution_success': iter_exec_success,
                    'has_code_error': iter_has_error,
                    'has_no_plan': iter_has_no_plan,
                    'itinerary': iter_structured.get('itinerary', []),
                    'original_output': iter_output
                })
            
            # Get the final iteration (last one)
            final_iteration = structured_iterations[-1] if structured_iterations else None
            final_itinerary = final_iteration.get('itinerary', []) if final_iteration else []
            
            # Determine if there was a successful iteration (one with a plan)
            has_successful_iteration = any(
                iter_item.get('execution_success', False) and 
                iter_item.get('itinerary', [])
                for iter_item in structured_iterations
            )
            
            structured_result = {
                'problem_id': result.get('problem_id'),
                'problem_index': result.get('problem_index'),
                'task_type': result.get('task_type'),
                'execution_success': result.get('execution_success', False),
                'structured_output': {"itinerary": final_itinerary},  # Final iteration result
                'original_output': result.get('output', ''),  # Final iteration output
                'golden_solution': result.get('golden_solution', ''),
                # Iterations data
                'iterations_data': {
                    'num_iterations': num_iterations,
                    'iterations': structured_iterations,
                    'final_itinerary': final_itinerary,
                    'final_iteration_index': num_iterations,
                    'has_successful_iteration': has_successful_iteration
                }
            }
        else:
            # No iterations data, treat as single iteration
            structured = convert_result_to_structured(result)
            
            structured_result = {
                'problem_id': result.get('problem_id'),
                'problem_index': result.get('problem_index'),
                'task_type': result.get('task_type'),
                'execution_success': result.get('execution_success', False),
                'structured_output': structured,
                'original_output': result.get('output', ''),
                'golden_solution': result.get('golden_solution', ''),
                # No iterations data
                'iterations_data': {
                    'num_iterations': 0,
                    'iterations': [],
                    'final_itinerary': structured.get('itinerary', []),
                    'final_iteration_index': None,
                    'has_successful_iteration': False
                }
            }
        
        structured_results.append(structured_result)
    
    # Determine output path
    if output_file:
        output_path = Path(output_file)
    else:
        # Save to new_results folder inside improved directory
        output_dir = Path(__file__).parent / "new_results"
        output_dir.mkdir(exist_ok=True)
        output_path = output_dir / f"{input_path.stem}_structured_iterations.json"
    
    # Save
    with open(output_path, 'w') as f:
        json.dump(structured_results, indent=2, fp=f)
    
    print(f"✓ Converted {len(structured_results)} results")
    print(f"✓ Saved to: {output_path}")
    
    # Print summary
    total_meetings = sum(len(r['structured_output']['itinerary']) for r in structured_results)
    non_empty = sum(1 for r in structured_results if r['structured_output']['itinerary'])
    
    # Iteration statistics
    total_iterations = sum(r['iterations_data']['num_iterations'] for r in structured_results)
    problems_with_iterations = sum(1 for r in structured_results if r['iterations_data']['num_iterations'] > 0)
    avg_iterations = total_iterations / len(structured_results) if structured_results else 0
    
    print(f"\nSummary:")
    print(f"  Total problems: {len(structured_results)}")
    print(f"  Problems with meetings: {non_empty}")
    print(f"  Total meetings extracted: {total_meetings}")
    print(f"  Average meetings per problem: {total_meetings/len(structured_results):.1f}")
    print(f"\nIteration Statistics:")
    print(f"  Problems with iterations: {problems_with_iterations}")
    print(f"  Total iterations: {total_iterations}")
    print(f"  Average iterations per problem: {avg_iterations:.2f}")
    
    # Show sample
    print(f"\nSample structured output (final iteration):")
    for i, result in enumerate(structured_results[:3]):
        if result['structured_output']['itinerary']:
            num_iterations = result['iterations_data']['num_iterations']
            iter_info = f" ({num_iterations} iterations)" if num_iterations > 0 else ""
            print(f"\n  Problem {i}: {result['problem_id']}{iter_info}")
            print(f"  {json.dumps(result['structured_output'], indent=4)}")
            break


def main():
    """Main function."""
    if len(sys.argv) < 2:
        print("Usage: python convert_to_structured_output_iterations.py <results_file.json> [output_file.json]")
        print("\nArguments:")
        print("  results_file  : Path to inference results JSON (from code_generation_inference_iterations.py)")
        print("  output_file   : Path to output file (optional, defaults to <input>_structured_iterations.json)")
        print("\nExample:")
        print("  python convert_to_structured_output_iterations.py code_generation_results/meeting_test_iterations.json")
        print("  python convert_to_structured_output_iterations.py results.json structured_results.json")
        sys.exit(1)
    
    input_file = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) > 2 else None
    
    process_results_file(input_file, output_file)
    
    print("\n" + "="*70)
    print("CONVERSION COMPLETE")
    print("="*70)


if __name__ == "__main__":
    main()
