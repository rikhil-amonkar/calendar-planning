from z3 import *
import json

# Define travel times (in minutes)
travel_times = {
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Financial District"): 26,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Financial District"): 19,
    ("Mission District", "Financial District"): 17,
}

# Friends data (excluding David since we can't meet him)
friends = {
    "Joseph": {
        "location": "Fisherman's Wharf",
        "start": 8 * 60,      # 8:00 AM
        "end": 17 * 60 + 30,  # 5:30 PM
        "duration": 90,
    },
    "Jeffrey": {
        "location": "Bayview",
        "start": 17 * 60 + 30,  # 5:30 PM
        "end": 21 * 60 + 30,    # 9:30 PM
        "duration": 60,
    },
    "Kevin": {
        "location": "Mission District",
        "start": 11 * 60 + 15,  # 11:15 AM
        "end": 15 * 60 + 15,    # 3:15 PM
        "duration": 30,
    },
    "Barbara": {
        "location": "Financial District",
        "start": 10 * 60 + 30,  # 10:30 AM
        "end": 16 * 60 + 30,    # 4:30 PM
        "duration": 15,
    },
}

# Initialize solver
s = Optimize()

# Create meeting time variables
meetings = {}
for person in friends:
    start = Int(f'start_{person}')
    end = Int(f'end_{person}')
    meetings[person] = {'start': start, 'end': end}
    s.add(start >= friends[person]['start'])
    s.add(end <= friends[person]['end'])
    s.add(end - start >= friends[person]['duration'])

# Starting point
current_time = 9 * 60  # 9:00 AM
current_location = "Golden Gate Park"

# Define possible meeting orders
possible_orders = [
    ["Barbara", "Kevin", "Joseph", "Jeffrey"],
    ["Kevin", "Barbara", "Joseph", "Jeffrey"],
    ["Barbara", "Joseph", "Kevin", "Jeffrey"],
]

# Try different meeting orders
for order in possible_orders:
    temp_solver = Solver()
    temp_meetings = {}
    
    # Create fresh variables for this attempt
    for person in friends:
        start = Int(f'temp_start_{person}')
        end = Int(f'temp_end_{person}')
        temp_meetings[person] = {'start': start, 'end': end}
        temp_solver.add(start >= friends[person]['start'])
        temp_solver.add(end <= friends[person]['end'])
        temp_solver.add(end - start >= friends[person]['duration'])
    
    # Add travel constraints
    prev_location = current_location
    prev_end = current_time
    
    for person in order:
        location = friends[person]['location']
        travel = travel_times.get((prev_location, location), 0)
        temp_solver.add(temp_meetings[person]['start'] >= prev_end + travel)
        prev_end = temp_meetings[person]['end']
        prev_location = location
    
    if temp_solver.check() == sat:
        model = temp_solver.model()
        itinerary = []
        for person in friends:
            start = model[temp_meetings[person]['start']].as_long()
            end = model[temp_meetings[person]['end']].as_long()
            start_time = f"{start//60:02d}:{start%60:02d}"
            end_time = f"{end//60:02d}:{end%60:02d}"
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": start_time,
                "end_time": end_time
            })
        itinerary.sort(key=lambda x: x['start_time'])
        print(json.dumps({"itinerary": itinerary}, indent=2))
        exit()

print("No valid schedule found with current constraints.")