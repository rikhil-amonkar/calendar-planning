from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define districts and their indices for easier reference
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
        [0, 9, 20, 22, 26, 21],    # Richmond to others
        [11, 0, 16, 17, 27, 16],    # Marina to others
        [20, 12, 0, 5, 22, 7],      # Chinatown to others
        [21, 15, 5, 0, 19, 9],      # Financial to others
        [25, 25, 18, 19, 0, 17],    # Bayview to others
        [20, 18, 7, 9, 15, 0]      # Union Square to others
    ]

    # Friends data: name, district, start_available, end_available, min_duration (minutes)
    friends = [
        ('Kimberly', 'Marina', 13*60 + 15, 16*60 + 45, 15),
        ('Robert', 'Chinatown', 12*60 + 15, 20*60 + 15, 15),
        ('Rebecca', 'Financial', 13*60 + 15, 16*60 + 45, 75),
        ('Margaret', 'Bayview', 9*60 + 30, 13*60 + 30, 30),
        ('Kenneth', 'Union Square', 19*60 + 30, 21*60 + 15, 75)
    ]

    # Current location starts at Richmond at 9:00 AM (540 minutes from midnight)
    current_location = districts['Richmond']
    current_time = 9 * 60  # 9:00 AM in minutes

    # Variables to track meetings
    meetings = []
    itinerary = []

    # For each friend, create start and end meeting times
    for i, (name, district, start_avail, end_avail, min_dur) in enumerate(friends):
        start_meet = Int(f'start_{name}')
        end_meet = Int(f'end_{name}')
        s.add(start_meet >= start_avail)
        s.add(end_meet <= end_avail)
        s.add(end_meet == start_meet + min_dur)
        meetings.append((name, district, start_meet, end_meet))

    # Ensure no overlapping meetings and travel times are respected
    for i in range(len(meetings)):
        name_i, district_i, start_i, end_i = meetings[i]
        # Constraint: arrival time at meeting i >= current_time + travel from previous location
        # First meeting's previous location is Richmond, current_time is 9:00 AM
        if i == 0:
            prev_location = current_location
            prev_end_time = current_time
        else:
            _, prev_district, _, prev_end = meetings[i-1]
            prev_location = districts[prev_district]
            prev_end_time = prev_end
        # Travel time from previous location to current meeting's location
        travel_time = travel_times[prev_location][districts[district_i]]
        s.add(start_i >= prev_end_time + travel_time)

        # Ensure this meeting doesn't overlap with others
        for j in range(i + 1, len(meetings)):
            name_j, district_j, start_j, end_j = meetings[j]
            # Either meeting i is before j or vice versa
            s.add(Or(end_i + travel_times[districts[district_i]][districts[district_j]] <= start_j,
                  end_j + travel_times[districts[district_j]][districts[district_i]] <= start_i))

    # Check if all constraints can be satisfied
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name, district, start_meet, end_meet in meetings:
            start_val = model.eval(start_meet).as_long()
            end_val = model.eval(end_meet).as_long()
            start_hh = start_val // 60
            start_mm = start_val % 60
            end_hh = end_val // 60
            end_mm = end_val % 60
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:])))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))