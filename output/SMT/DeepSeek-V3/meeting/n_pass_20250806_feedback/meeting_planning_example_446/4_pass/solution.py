from z3 import *
import json
from datetime import datetime, timedelta

def solve_scheduling():
    # Initialize solver with a longer timeout
    s = Solver()
    s.set("timeout", 60000)  # 60 second timeout

    # Define districts and their indices
    districts = {
        'Richmond': 0,
        'Marina': 1,
        'Chinatown': 2,
        'Financial': 3,
        'Bayview': 4,
        'Union Square': 5
    }

    # Travel times matrix (minutes)
    travel_times = [
        [0, 9, 20, 22, 26, 21],    # Richmond
        [11, 0, 16, 17, 27, 16],    # Marina
        [20, 12, 0, 5, 22, 7],      # Chinatown
        [21, 15, 5, 0, 19, 9],      # Financial
        [25, 25, 18, 19, 0, 17],    # Bayview
        [20, 18, 7, 9, 15, 0]       # Union Square
    ]

    # Friends data with priority based on duration
    friends = [
        ('Rebecca', 'Financial', 13*60+15, 16*60+45, 75),
        ('Kenneth', 'Union Square', 19*60+30, 21*60+15, 75),
        ('Margaret', 'Bayview', 9*60+30, 13*60+30, 30),
        ('Kimberly', 'Marina', 13*60+15, 16*60+45, 15),
        ('Robert', 'Chinatown', 12*60+15, 20*60+15, 15)
    ]

    # Current state
    current_location = districts['Richmond']
    current_time = 9 * 60  # 9:00 AM in minutes

    # Create meeting variables
    meetings = []
    for name, district, start_avail, end_avail, min_dur in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        s.add(start >= start_avail)
        s.add(end <= end_avail)
        s.add(end == start + min_dur)
        meetings.append((name, district, start, end))

    # Add sequencing constraints
    for i in range(len(meetings)):
        name_i, district_i, start_i, end_i = meetings[i]
        
        # First meeting must be reachable from starting point
        if i == 0:
            travel = travel_times[current_location][districts[district_i]]
            s.add(start_i >= current_time + travel)
        else:
            # Subsequent meetings must account for travel from previous
            _, prev_district, _, prev_end = meetings[i-1]
            travel = travel_times[districts[prev_district]][districts[district_i]]
            s.add(start_i >= prev_end + travel)

    # Add non-overlap constraints
    for i in range(len(meetings)):
        for j in range(i+1, len(meetings)):
            name_i, district_i, start_i, end_i = meetings[i]
            name_j, district_j, start_j, end_j = meetings[j]
            
            # Either i is before j or j is before i
            s.add(Or(
                end_i + travel_times[districts[district_i]][districts[district_j]] <= start_j,
                end_j + travel_times[districts[district_j]][districts[district_i]] <= start_i
            ))

    # Try to solve
    result = s.check()
    if result == sat:
        model = s.model()
        itinerary = []
        for name, district, start, end in meetings:
            start_val = model.eval(start).as_long()
            end_val = model.eval(end).as_long()
            start_time = f"{start_val//60:02d}:{start_val%60:02d}"
            end_time = f"{end_val//60:02d}:{end_val%60:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time,
                "location": district
            })
        
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"status": "success", "itinerary": itinerary}
    elif result == unsat:
        return {"status": "failed", "reason": "No possible schedule meets all constraints"}
    else:
        return {"status": "unknown", "reason": "Solver could not determine satisfiability"}

# Run and print results
result = solve_scheduling()
print(json.dumps(result, indent=2))