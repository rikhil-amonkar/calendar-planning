#!/usr/bin/env python3
"""
Convert text-based itinerary outputs to structured JSON format with iteration information.

This version processes iterations and includes detailed information about each attempt.

Output format includes:
- Final structured output (from final successful iteration)
- All iterations with their structured outputs
- Iteration metadata (success, errors, etc.)
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
    
    # Handle case where text is a list representation (string)
    if isinstance(text, str) and text.startswith('[') and text.endswith(']'):
        # Try to parse as Python list
        try:
            import ast
            text_list = ast.literal_eval(text)
            if isinstance(text_list, list):
                text = '\n'.join(str(item) for item in text_list)
        except:
            pass
    
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


def convert_iteration_to_structured(iteration: Dict) -> Dict:
    """
    Convert a single iteration to structured format.
    
    Args:
        iteration: Iteration dictionary with 'output' field
    
    Returns:
        Dictionary with structured output and metadata
    """
    output_text = iteration.get('output', '')
    
    # Check if execution failed
    if not output_text or output_text.startswith('Traceback') or 'error' in output_text.lower()[:50]:
        return {
            "itinerary": [],
            "execution_success": False,
            "has_error": True
        }
    
    meetings = extract_meetings_from_text(output_text)
    
    return {
        "itinerary": meetings,
        "execution_success": iteration.get('execution_success', False),
        "has_error": iteration.get('has_execution_error', False),
        "has_no_plan": iteration.get('has_no_plan', False)
    }


def convert_result_to_structured_with_iterations(result: Dict) -> Dict:
    """
    Convert a result entry with iterations to structured format.
    
    Args:
        result: Result dictionary with 'output' and 'iterations' fields
    
    Returns:
        Structured output with final result and all iterations
    """
    iterations = result.get('iterations', [])
    
    # Process all iterations
    structured_iterations = []
    final_iteration_output = None
    final_iteration_index = None
    
    for i, iteration in enumerate(iterations):
        structured_iter = convert_iteration_to_structured(iteration)
        
        # Add iteration metadata
        structured_iter['iteration_number'] = iteration.get('iteration', i + 1)
        structured_iter['code'] = iteration.get('code', '')
        structured_iter['model_response'] = iteration.get('model_response', '')
        structured_iter['error_output'] = iteration.get('error_output', '')
        structured_iter['will_retry'] = iteration.get('will_retry', False)
        structured_iter['stopped_reason'] = iteration.get('stopped_reason')
        
        structured_iterations.append(structured_iter)
        
        # Track the final successful iteration (or last iteration if none succeeded)
        if structured_iter['execution_success'] and structured_iter['itinerary']:
            final_iteration_output = structured_iter['itinerary']
            final_iteration_index = i
        elif final_iteration_output is None:
            # Keep track of last iteration even if it failed
            final_iteration_output = structured_iter['itinerary']
            final_iteration_index = i
    
    # If no iterations, fall back to top-level output
    if not iterations:
        output_text = result.get('output', '')
        if output_text and not output_text.startswith('Traceback'):
            final_iteration_output = extract_meetings_from_text(output_text)
        else:
            final_iteration_output = []
    
    return {
        "final_itinerary": final_iteration_output or [],
        "final_iteration_index": final_iteration_index,
        "iterations": structured_iterations,
        "num_iterations": len(iterations),
        "has_successful_iteration": any(
            iter_data.get('execution_success', False) and iter_data.get('itinerary', [])
            for iter_data in structured_iterations
        )
    }


def process_results_file(input_file: str, output_file: Optional[str] = None) -> None:
    """
    Process a results JSON file and convert all outputs to structured format with iterations.
    
    Args:
        input_file: Path to input JSON file
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
        structured = convert_result_to_structured_with_iterations(result)
        
        # Add metadata
        structured_result = {
            'problem_id': result.get('problem_id'),
            'problem_index': result.get('problem_index'),
            'task_type': result.get('task_type'),
            'execution_success': result.get('execution_success', False),
            'success': result.get('success', False),
            'structured_output': {
                'itinerary': structured['final_itinerary']
            },
            'iterations_data': structured,
            'original_output': result.get('output', ''),
            'golden_solution': result.get('golden_solution', '')
        }
        
        structured_results.append(structured_result)
    
    # Determine output path
    if output_file:
        output_path = Path(output_file)
    else:
        # Save to structured_results folder (one level up from input file's directory)
        # If input is in code_generation_results/, go up one level to improved/, then into structured_results/
        structured_results_dir = input_path.parent.parent / "structured_results"
        
        # Create directory if it doesn't exist
        structured_results_dir.mkdir(exist_ok=True)
        
        output_path = structured_results_dir / f"{input_path.stem}_structured_iterations.json"
    
    # Save
    with open(output_path, 'w') as f:
        json.dump(structured_results, indent=2, fp=f)
    
    print(f"✓ Converted {len(structured_results)} results")
    print(f"✓ Saved to: {output_path}")
    
    # Print summary
    total_meetings = sum(len(r['structured_output']['itinerary']) for r in structured_results)
    non_empty = sum(1 for r in structured_results if r['structured_output']['itinerary'])
    total_iterations = sum(r['iterations_data']['num_iterations'] for r in structured_results)
    successful_iterations = sum(
        1 for r in structured_results 
        if r['iterations_data']['has_successful_iteration']
    )
    
    print(f"\nSummary:")
    print(f"  Total problems: {len(structured_results)}")
    print(f"  Problems with meetings (final): {non_empty}")
    print(f"  Total meetings extracted (final): {total_meetings}")
    print(f"  Average meetings per problem: {total_meetings/len(structured_results):.1f}")
    print(f"  Total iterations across all problems: {total_iterations}")
    print(f"  Problems with successful iterations: {successful_iterations}")
    print(f"  Average iterations per problem: {total_iterations/len(structured_results):.1f}")
    
    # Show sample
    print(f"\nSample structured output:")
    for i, result in enumerate(structured_results[:3]):
        if result['structured_output']['itinerary']:
            print(f"\n  Problem {i}: {result['problem_id']}")
            print(f"  Iterations: {result['iterations_data']['num_iterations']}")
            print(f"  Final iteration index: {result['iterations_data']['final_iteration_index']}")
            print(f"  Has successful iteration: {result['iterations_data']['has_successful_iteration']}")
            print(f"  Final itinerary: {len(result['structured_output']['itinerary'])} meetings")
            break


def main():
    """Main function."""
    if len(sys.argv) < 2:
        print("Usage: python convert_to_structured_output_iterations.py <results_file.json> [output_file.json]")
        print("\nArguments:")
        print("  results_file  : Path to inference results JSON (with iterations)")
        print("  output_file   : Path to output file (optional, defaults to <input>_structured_iterations.json)")
        print("\nExample:")
        print("  python convert_to_structured_output_iterations.py code_generation_results/meeting_test_run.json")
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
