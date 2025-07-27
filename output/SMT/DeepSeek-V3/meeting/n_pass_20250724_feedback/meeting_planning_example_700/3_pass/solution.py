from z3 import *
import json

# Define the travel times between locations (in minutes)
travel_times = {
    "Presidio": {
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Fisherman's Wharf": 19,
        "Marina District": 11,
        "Alamo Square": 19,
        "Sunset District": 15,
        "Nob Hill": 18,
        "North Beach": 18
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Alamo Square": 10,
        "Sunset District": 21,
        "Nob Hill": 8,
        "North Beach": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Pacific Heights": 16,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Alamo Square": 9,
        "Sunset District": 10,
        "Nob Hill": 20,
        "North Beach": 23
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Pacific Heights": 12,
        "Golden Gate Park": 25,
        "Marina District": 9,
        "Alamo Square": 21,
        "Sunset District": 27,
        "Nob Hill": 11,
        "North Beach": 6
    },
    "Marina District": {
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Fisherman's Wharf": 10,
        "Alamo Square": 15,
        "Sunset District": 19,
        "Nob Hill": 12,
        "North Beach": 11
    },
    "Alamo Square": {
        "Presidio": 17,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Fisherman's Wharf": 19,
        "Marina District": 15,
        "Sunset District": 16,
        "Nob Hill": 11,
        "North Beach": 15
    },
    "Sunset District": {
        "Presidio": 16,
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "Marina District": 21,
        "Alamo Square": 17,
        "Nob Hill": 27,
        "North Beach": 28
    },
    "Nob Hill": {
        "Presidio": 17,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Fisherman's Wharf": 10,
        "Marina District": 11,
        "Alamo Square": 11,
        "Sunset District": 24,
        "North Beach": 8
    },
    "North Beach": {
        "Presidio": 17,
        "Pacific Heights": 8,
        "Golden Gate Park": 22,
        "Fisherman's Wharf": 5,
        "Marina District": 9,
        "Alamo Square": 16,
        "Sunset District": 27,
        "Nob Hill": 7
    }
}

# Friends' availability and meeting constraints
friends = {
    "Michelle": {
        "location": "Golden Gate Park",
        "start": "20:00",
        "end": "21:00",
        "duration": 15
    },
    "Emily": {
        "location": "Fisherman's Wharf",
        "start": "16:15",
        "end": "19:00",
        "duration": 30
    },
    "Mark": {
        "location": "Marina District",
        "start": "18:15",
        "end": "19:45",
        "duration": 75
    },
    "Barbara": {
        "location": "Alamo Square",
        "start": "17:00",
        "end": "19:00",
        "duration": 120
    },
    "Laura": {
        "location": "Sunset District",
        "start": "19:00",
        "end": "21:15",
        "duration": 75
    },
    "Mary": {
        "location": "Nob Hill",
        "start": "17:30",
        "end": "19:00",
        "duration": 45
    },
    "Helen": {
        "location": "North Beach",
        "start": "11:00",
        "end": "12:15",
        "duration": 45
    }
}

# Convert time string to minutes since 9:00 AM (540 minutes)
def time_to_minutes(time_str):
    hh, mm = map(int, time_str.split(':'))
    return hh * 60 + mm - 540  # Subtract 540 to start from 9:00 AM (540 minutes)

# Convert minutes back to time string
def minutes_to_time(minutes):
    total_minutes = 540 + minutes
    hh = total_minutes // 60
    mm = total_minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Initialize Z3 solver
solver = Solver()

# Create variables for each meeting's start and end times
meetings = {}
for name in friends:
    start = Int(f"start_{name}")
    end = Int(f"end_{name}")
    meetings[name] = {"start": start, "end": end}

# Add constraints for each meeting
for name, data in friends.items():
    start_min = time_to_minutes(data["start"])
    end_min = time_to_minutes(data["end"])
    duration = data["duration"]
    
    solver.add(meetings[name]["start"] >= start_min)
    solver.add(meetings[name]["end"] <= end_min)
    solver.add(meetings[name]["end"] == meetings[name]["start"] + duration)

# Define the order of meetings as a permutation
# We'll use a list to represent the order and ensure no overlaps
order = [name for name in friends]
n = len(order)

# Add constraints to ensure no overlaps and travel times are respected
for i in range(n):
    for j in range(i + 1, n):
        # For each pair of meetings, ensure one is before the other with travel time
        name1 = order[i]
        name2 = order[j]
        loc1 = friends[name1]["location"]
        loc2 = friends[name2]["location"]
        travel_time = travel_times[loc1][loc2]
        
        # Either name1 is before name2 or vice versa
        before = And(
            meetings[name1]["end"] + travel_time <= meetings[name2]["start"]
        )
        after = And(
            meetings[name2]["end"] + travel_times[loc2][loc1] <= meetings[name1]["start"]
        )
        solver.add(Or(before, after))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends:
        start = model.evaluate(meetings[name]["start"]).as_long()
        end = model.evaluate(meetings[name]["end"]).as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"itinerary": []}, indent=2))