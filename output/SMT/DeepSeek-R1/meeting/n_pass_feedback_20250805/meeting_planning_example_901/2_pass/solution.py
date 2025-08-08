import json
from z3 import *

def main():
    # Read the meetings from meetings.json
    with open('meetings.json', 'r') as f:
        meetings_data = json.load(f)
    
    # Read travel times from travel_times.json
    with open('travel_times.json', 'r') as f:
        travel_dict = json.load(f)
        # Convert keys back to tuples because json converts them to arrays
        travel_dict = {tuple(k): v for k, v in travel_dict.items()}
    
    home = "Home"
    
    # Build set of all locations (home and meeting locations)
    all_locations_set = set()
    all_locations_set.add(home)
    for meeting in meetings_data:
        all_locations_set.add(meeting['location'])
    
    # Add self-loops with 0 travel time for all locations
    for loc in all_locations_set:
        travel_dict[(loc, loc)] = 0
    
    # Add fixed meetings: at the start (home) and at the end (home)
    meetings = [{'name': 'Start', 'location': home, 'duration': 0, 'earliest': 0, 'latest': 0}] + meetings_data
    meetings.append({'name': 'End', 'location': home, 'duration': 0, 'earliest': 0, 'latest': 24*60})
    
    # Get unique locations
    unique_locations = list(all_locations_set)
    n = len(unique_locations)
    num_meetings = len(meetings)
    
    # Create a travel time matrix for the TSP
    travel_matrix = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            from_loc = unique_locations[i]
            to_loc = unique_locations[j]
            travel_matrix[i][j] = travel_dict[(from_loc, to_loc)]
    
    # Create location to index mapping
    loc_to_index = {loc: idx for idx, loc in enumerate(unique_locations)}
    
    # Initialize Z3 variables
    start_times = [Int(f'start_{i}') for i in range(num_meetings)]
    end_times = [Int(f'end_{i}') for i in range(num_meetings)]
    
    # Path variables: the index of the meeting in the sequence
    path = [Int(f'path_{i}') for i in range(num_meetings)]
    
    # Create solver
    s = Solver()
    
    # Constraints for start and end times
    for i, meeting in enumerate(meetings):
        s.add(start_times[i] >= meeting['earliest'])
        s.add(start_times[i] <= meeting['latest'])
        s.add(end_times[i] == start_times[i] + meeting['duration'])
    
    # Start and end meetings are fixed in position
    s.add(path[0] == 0)  # Start meeting is first
    s.add(path[num_meetings-1] == num_meetings-1)  # End meeting is last
    
    # All meetings must be visited exactly once
    s.add(Distinct(path))
    
    # Meeting ordering constraints
    for idx in range(num_meetings-1):
        i = path[idx]
        j = path[idx+1]
        
        # Location indices for travel time lookup
        from_loc_idx = loc_to_index[meetings[i]['location']]
        to_loc_idx = loc_to_index[meetings[j]['location']]
        travel_time = travel_matrix[from_loc_idx][to_loc_idx]
        
        s.add(start_times[j] >= end_times[i] + travel_time)
    
    # Set path bounds: each path variable must be between 0 and num_meetings-1
    for p in path:
        s.add(p >= 0)
        s.add(p < num_meetings)
    
    # Check and get solution
    if s.check() == sat:
        model = s.model()
        start_vals = [model.eval(start_times[i]).as_long() for i in range(num_meetings)]
        path_vals = [model.eval(path[i]).as_long() for i in range(num_meetings)]
        
        # Print schedule in order
        print("Schedule:")
        for idx in range(num_meetings):
            i = path_vals[idx]
            start = start_vals[i]
            hours, minutes = divmod(start, 60)
            print(f"{meetings[i]['name']}: starts at {hours:02d}:{minutes:02d}, location: {meetings[i]['location']}")
    else:
        print("No valid schedule found")

if __name__ == '__main__':
    main()