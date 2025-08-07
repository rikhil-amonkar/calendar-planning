import json
from z3 import *
import os

def main():
    # Get the directory where the script is located
    script_dir = os.path.dirname(os.path.abspath(__file__))
    
    # Construct full paths to JSON files
    meetings_path = os.path.join(script_dir, 'meetings.json')
    travel_times_path = os.path.join(script_dir, 'travel_times.json')
    
    # Read meetings data
    try:
        with open(meetings_path, 'r') as f:
            meetings_data = json.load(f)
    except FileNotFoundError:
        print(f"Error: Could not find meetings.json at {meetings_path}")
        return
    
    # Read travel times data
    try:
        with open(travel_times_path, 'r') as f:
            travel_dict = json.load(f)
            travel_dict = {tuple(k): v for k, v in travel_dict.items()}
    except FileNotFoundError:
        print(f"Error: Could not find travel_times.json at {travel_times_path}")
        return
    
    home = "Home"
    
    # Build set of all locations
    all_locations_set = {home}
    for meeting in meetings_data:
        all_locations_set.add(meeting['location'])
    
    # Add self-loops with 0 travel time
    for loc in all_locations_set:
        travel_dict.setdefault((loc, loc), 0)
    
    # Add fixed meetings
    meetings = [{'name': 'Start', 'location': home, 'duration': 0, 'earliest': 0, 'latest': 0}] 
    meetings += meetings_data
    meetings.append({'name': 'End', 'location': home, 'duration': 0, 'earliest': 0, 'latest': 24*60})
    
    # Get unique locations and create mapping
    unique_locations = list(all_locations_set)
    loc_to_index = {loc: idx for idx, loc in enumerate(unique_locations)}
    n = len(unique_locations)
    num_meetings = len(meetings)
    
    # Create travel time matrix
    travel_matrix = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            from_loc = unique_locations[i]
            to_loc = unique_locations[j]
            travel_matrix[i][j] = travel_dict.get((from_loc, to_loc), 0)
    
    # Initialize Z3 variables
    start_times = [Int(f'start_{i}') for i in range(num_meetings)]
    end_times = [Int(f'end_{i}') for i in range(num_meetings)]
    path = [Int(f'path_{i}') for i in range(num_meetings)]
    
    # Create solver
    s = Solver()
    
    # Time window constraints
    for i, meeting in enumerate(meetings):
        s.add(start_times[i] >= meeting['earliest'])
        s.add(start_times[i] <= meeting['latest'])
        s.add(end_times[i] == start_times[i] + meeting['duration'])
    
    # Path constraints
    s.add(path[0] == 0)  # Start meeting first
    s.add(path[-1] == num_meetings - 1)  # End meeting last
    s.add(Distinct(path))
    
    # Meeting ordering constraints
    for idx in range(num_meetings - 1):
        i = path[idx]
        j = path[idx + 1]
        
        from_idx = loc_to_index[meetings[i]['location']]
        to_idx = loc_to_index[meetings[j]['location']]
        travel_time = travel_matrix[from_idx][to_idx]
        
        s.add(start_times[j] >= end_times[i] + travel_time)
    
    # Path bounds
    for p in path:
        s.add(p >= 0, p < num_meetings)
    
    # Solve and output
    if s.check() == sat:
        model = s.model()
        start_vals = [model.eval(t).as_long() for t in start_times]
        path_vals = [model.eval(p).as_long() for p in path]
        
        # Print schedule in order
        print("Optimal Schedule:")
        for idx in range(num_meetings):
            meeting_idx = path_vals[idx]
            name = meetings[meeting_idx]['name']
            loc = meetings[meeting_idx]['location']
            start = start_vals[meeting_idx]
            hours, minutes = divmod(start, 60)
            print(f"{name}: {hours:02d}:{minutes:02d} at {loc}")
    else:
        print("No valid schedule exists")

if __name__ == '__main__':
    main()