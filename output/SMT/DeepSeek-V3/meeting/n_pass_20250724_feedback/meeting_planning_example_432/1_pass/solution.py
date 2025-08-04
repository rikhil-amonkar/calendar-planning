from z3 import *
import json

# Define the travel times between locations
travel_times = {
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Financial District"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Financial District"): 19,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Financial District"): 17,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Financial District"): 5,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Embarcadero"): 4,
}

# Define friends and their availability
friends = {
    "Joseph": {
        "location": "Fisherman's Wharf",
        "start": 8 * 60,  # 8:00 AM
        "end": 17 * 60 + 30,  # 5:30 PM
        "duration": 90,
    },
    "Jeffrey": {
        "location": "Bayview",
        "start": 17 * 60 + 30,  # 5:30 PM
        "end": 21 * 60 + 30,  # 9:30 PM
        "duration": 60,
    },
    "Kevin": {
        "location": "Mission District",
        "start": 11 * 60 + 15,  # 11:15 AM
        "end": 15 * 60 + 15,  # 3:15 PM
        "duration": 30,
    },
    "David": {
        "location": "Embarcadero",
        "start": 8 * 60 + 15,  # 8:15 AM
        "end": 9 * 60,  # 9:00 AM
        "duration": 30,
    },
    "Barbara": {
        "location": "Financial District",
        "start": 10 * 60 + 30,  # 10:30 AM
        "end": 16 * 60 + 30,  # 4:30 PM
        "duration": 15,
    },
}

# Initialize Z3 solver
s = Solver()

# Create variables for each meeting's start and end times
meetings = {}
for person in friends:
    start = Int(f"start_{person}")
    end = Int(f"end_{person}")
    meetings[person] = {"start": start, "end": end}
    # Constraint: meeting duration must be at least the required duration
    s.add(end - start >= friends[person]["duration"])
    # Constraint: meeting must be within friend's availability
    s.add(start >= friends[person]["start"])
    s.add(end <= friends[person]["end"])

# Constraint: you start at Golden Gate Park at 9:00 AM (540 minutes)
current_time = 9 * 60
current_location = "Golden Gate Park"

# Order of meetings to consider (this can be adjusted for optimization)
meeting_order = ["David", "Barbara", "Kevin", "Joseph", "Jeffrey"]

# Add constraints for travel times between meetings
for i in range(len(meeting_order)):
    person = meeting_order[i]
    location = friends[person]["location"]
    # Travel from current_location to friend's location
    travel_time = travel_times[(current_location, location)]
    # Constraint: start time of next meeting >= end time of previous + travel time
    if i == 0:
        s.add(meetings[person]["start"] >= current_time + travel_time)
    else:
        prev_person = meeting_order[i - 1]
        s.add(meetings[person]["start"] >= meetings[prev_person]["end"] + travel_time)
    current_location = location

# Ensure all meetings are scheduled
for person in friends:
    s.add(meetings[person]["start"] >= 0)
    s.add(meetings[person]["end"] >= 0)

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    itinerary = []
    for person in friends:
        start = model[meetings[person]["start"]].as_long()
        end = model[meetings[person]["end"]].as_long()
        start_time = f"{start // 60:02d}:{start % 60:02d}"
        end_time = f"{end // 60:02d}:{end % 60:02d}"
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": start_time,
            "end_time": end_time
        })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid schedule found.")