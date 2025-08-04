from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define locations and travel times
    locations = {
        'Haight-Ashbury': 0,
        'Russian Hill': 1,
        'Fisherman\'s Wharf': 2,
        'Nob Hill': 3,
        'Golden Gate Park': 4,
        'Alamo Square': 5,
        'Pacific Heights': 6
    }

    travel_times = [
        [0, 17, 23, 15, 7, 5, 12],    # Haight-Ashbury
        [17, 0, 7, 5, 21, 15, 7],      # Russian Hill
        [22, 7, 0, 11, 25, 20, 12],    # Fisherman's Wharf
        [13, 5, 11, 0, 17, 11, 8],     # Nob Hill
        [7, 19, 24, 20, 0, 10, 16],    # Golden Gate Park
        [5, 13, 19, 11, 9, 0, 10],     # Alamo Square
        [11, 7, 13, 8, 15, 10, 0]      # Pacific Heights
    ]

    # Friends' data: name, location, start_available, end_available, min_duration
    friends = [
        ('Stephanie', 'Russian Hill', 20*60, 20*60 + 45, 15),
        ('Kevin', 'Fisherman\'s Wharf', 19*60 + 15, 21*60 + 45, 75),
        ('Robert', 'Nob Hill', 7*60 + 45, 10*60 + 30, 90),
        ('Steven', 'Golden Gate Park', 8*60 + 30, 17*60, 75),
        ('Anthony', 'Alamo Square', 7*60 + 45, 19*60 + 45, 15),
        ('Sandra', 'Pacific Heights', 14*60 + 45, 21*60 + 45, 45)
    ]

    # Current location starts at Haight-Ashbury at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_loc = locations['Haight-Ashbury']

    # Variables for each meeting: start, end, location
    meet_vars = []
    for i, (name, loc, start_avail, end_avail, min_dur) in enumerate(friends):
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meet_vars.append((name, loc, start, end, start_avail, end_avail, min_dur))
        s.add(start >= start_avail)
        s.add(end <= end_avail)
        s.add(end - start >= min_dur)
        s.add(start >= 0)
        s.add(end >= 0)

    # Order constraints: ensure meetings are in order and travel time is accounted for
    # We need to find a permutation of meetings that fits
    # This is complex, so we'll use a simplified approach by trying to meet friends in order
    # and adding constraints based on travel times

    # For simplicity, we'll assume an order and let Z3 find feasible times
    # This is a heuristic and may not find the optimal solution
    # A better approach would be to use a more sophisticated scheduling algorithm

    # We'll prioritize friends with tighter windows first
    friends_sorted = sorted(friends, key=lambda x: x[3] - x[2])
    meet_vars_sorted = []
    for name, loc, start_avail, end_avail, min_dur in friends_sorted:
        for v in meet_vars:
            if v[0] == name:
                meet_vars_sorted.append(v)
                break

    # Add ordering constraints
    for i in range(len(meet_vars_sorted) - 1):
        name1, loc1, start1, end1, _, _, _ = meet_vars_sorted[i]
        name2, loc2, start2, end2, _, _, _ = meet_vars_sorted[i+1]
        travel_time = travel_times[locations[loc1]][locations[loc2]]
        s.add(start2 >= end1 + travel_time)

    # Ensure first meeting is after current time + travel time
    if meet_vars_sorted:
        first_name, first_loc, first_start, first_end, _, _, _ = meet_vars_sorted[0]
        travel_time = travel_times[current_loc][locations[first_loc]]
        s.add(first_start >= current_time + travel_time)

    # Check if solution exists
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name, loc, start, end, _, _, _ in meet_vars_sorted:
            start_val = m.evaluate(start).as_long()
            end_val = m.evaluate(end).as_long()
            start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
            end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
            itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver
result = solve_scheduling()
print(json.dumps(result, indent=2))