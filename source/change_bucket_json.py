import json
import re

def parse_file(filename):
    with open(filename, 'r') as f:
        content = f.read()
    
    # Split into sections
    sections = re.split(r'=+\s[\d-]+%\sMost Constrained\s=+', content)
    if len(sections) != 6:
        print(f"Warning: Expected 5 sections in {filename}, found {len(sections)-1}")
    
    buckets = []
    for i, section in enumerate(sections[1:]):  # Skip the header section
        lines = [line.strip() for line in section.split('\n') if line.strip()]
        bucket = []
        for line in lines:
            # Extract filename and constraint count
            match = re.match(r'^(.+?): (\d+) constraints$', line)
            if match:
                filename = match.group(1)
                # Remove _output.json and any other suffixes if present
                file_id = re.sub(r'_output\.json$', '', filename)
                num_constraints = int(match.group(2))
                bucket.append({
                    "id": file_id,
                    "num_constraints": num_constraints
                })
        # Sort each bucket by num_constraints in ascending order
        bucket.sort(key=lambda x: x["num_constraints"])
        buckets.append(bucket)
    
    # Reverse the buckets to put least constrained first
    return buckets[::-1]

def create_json_structure(calendar_buckets, trip_buckets, meeting_buckets):
    result = {
        "calendar": {},
        "trip": {},
        "meeting": {}
    }
    
    descriptions = [
        "0-20% (Least Constrained)",
        "20-40%",
        "40-60%",
        "60-80%",
        "80-100% (Most Constrained)"
    ]
    
    for i in range(5):
        bucket_name = f"bucket{i}"
        result["calendar"][bucket_name] = {
            "description": descriptions[i],
            "content": calendar_buckets[i] if i < len(calendar_buckets) else []
        }
        result["trip"][bucket_name] = {
            "description": descriptions[i],
            "content": trip_buckets[i] if i < len(trip_buckets) else []
        }
        result["meeting"][bucket_name] = {
            "description": descriptions[i],
            "content": meeting_buckets[i] if i < len(meeting_buckets) else []
        }
    
    return result

def main():
    # ====== EDIT THESE FILENAMES DIRECTLY IN THE CODE ======
    input_files = {
        "calendar": "bucketed_constraints/constraint_summary_calendar.txt",  # Change to your calendar input file
        "trip": "bucketed_constraints/constraint_summary_trip.txt",        # Change to your trip input file
        "meeting": "bucketed_constraints/constraint_summary_meeting.txt"   # Change to your meeting input file
    }
    output_file = "bucketed_constraints/bucketed_constraints_all_tasks.json"    # Change to your desired output file
    # ======================================================
    
    try:
        # Parse all input files
        calendar_buckets = parse_file(input_files["calendar"])
        trip_buckets = parse_file(input_files["trip"])
        meeting_buckets = parse_file(input_files["meeting"])
        
        # Create the JSON structure
        json_structure = create_json_structure(calendar_buckets, trip_buckets, meeting_buckets)
        
        # Write to output file
        with open(output_file, 'w') as f:
            json.dump(json_structure, f, indent=4)
        
        print(f"Successfully created {output_file}")
        
    except FileNotFoundError as e:
        print(f"Error: File not found - {e.filename}")
    except Exception as e:
        print(f"Error: {e}")

if __name__ == "__main__":
    main()

