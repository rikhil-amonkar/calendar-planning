from z3 import *
import json

# Define the travel times between locations (in minutes)
travel_times = {
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Financial District": 5,
        "Russian Hill": 8,
        "Marina District": 12,
        "Richmond District": 21,
        "Pacific Heights": 11,
        "Haight-Ashbury": 21,
        "Presidio": 20,
        "Nob Hill": 10,
        "The Castro": 25
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Financial District": 11,
        "Russian Hill": 7,
        "Marina District": 9,
        "Richmond District": 18,
        "Pacific Heights": 12,
        "Haight-Ashbury": 22,
        "Presidio": 17,
        "Nob Hill": 11,
        "The Castro": 27
    },
    "Financial District": {
        "Embarcadero": 4,
        "Fisherman's Wharf": 10,
        "Russian Hill": 11,
        "Marina District": 15,
        "Richmond District": 21,
        "Pacific Heights": 13,
        "Haight-Ashbury": 19,
        "Presidio": 22,
        "Nob Hill": 8,
        "The Castro": 20
    },
    "Russian Hill": {
        "Embarcadero": 8,
        "Fisherman's Wharf": 7,
        "Financial District": 11,
        "Marina District": 7,
        "Richmond District": 14,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Presidio": 14,
        "Nob Hill": 5,
        "The Castro": 21
    },
    "Marina District": {
        "Embarcadero": 14,
        "Fisherman's Wharf": 10,
        "Financial District": 17,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Pacific Heights": 7,
        "Haight-Ashbury": 16,
        "Presidio": 10,
        "Nob Hill": 12,
        "The Castro": 22
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Fisherman's Wharf": 18,
        "Financial District": 22,
        "Russian Hill": 13,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Presidio": 7,
        "Nob Hill": 17,
        "The Castro": 16
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Fisherman's Wharf": 13,
        "Financial District": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "Richmond District": 12,
        "Haight-Ashbury": 11,
        "Presidio": 11,
        "Nob Hill": 8,
        "The Castro": 16
    },
    "Haight-Ashbury": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Financial District": 21,
        "Russian Hill": 17,
        "Marina District": 17,
        "Richmond District": 10,
        "Pacific Heights": 12,
        "Presidio": 15,
        "Nob Hill": 15,
        "The Castro": 6
    },
    "Presidio": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 19,
        "Financial District": 23,
        "Russian Hill": 14,
        "Marina District": 11,
        "Richmond District": 7,
        "Pacific Heights": 11,
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "The Castro": 21
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Fisherman's Wharf": 10,
        "Financial District": 9,
        "Russian Hill": 5,
        "Marina District": 11,
        "Richmond District": 14,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Presidio": 17,
        "The Castro": 16
    },
    "The Castro": {
        "Embarcadero": 22,
        "Fisherman's Wharf": 24,
        "Financial District": 21,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Presidio": 20,
        "Nob Hill": 16
    }
}

# Define friends' availability and meeting constraints
friends = {
    "Stephanie": {
        "location": "Fisherman's Wharf",
        "start": 15 * 60 + 30,  # 3:30 PM in minutes
        "end": 22 * 60,         # 10:00 PM in minutes
        "duration": 30          # 30 minutes
    },
    "Lisa": {
        "location": "Financial District",
        "start": 10 * 60 + 45,  # 10:45 AM in minutes
        "end": 17 * 60 + 15,    # 5:15 PM in minutes
        "duration": 15          # 15 minutes
    },
    "Melissa": {
        "location": "Russian Hill",
        "start": 17 * 60,      # 5:00 PM in minutes
        "end": 21 * 60 + 45,    # 9:45 PM in minutes
        "duration": 120         # 120 minutes
    },
    "Betty": {
        "location": "Marina District",
        "start": 10 * 60 + 45,  # 10:45 AM in minutes
        "end": 14 * 60 + 15,    # 2:15 PM in minutes
        "duration": 60          # 60 minutes
    },
    "Sarah": {
        "location": "Richmond District",
        "start": 16 * 60 + 15,  # 4:15 PM in minutes
        "end": 19 * 60 + 30,    # 7:30 PM in minutes
        "duration": 105         # 105 minutes
    },
    "Daniel": {
        "location": "Pacific Heights",
        "start": 18 * 60 + 30,  # 6:30 PM in minutes
        "end": 21 * 60 + 45,    # 9:45 PM in minutes
        "duration": 60          # 60 minutes
    },
    "Joshua": {
        "location": "Haight-Ashbury",
        "start": 9 * 60,       # 9:00 AM in minutes
        "end": 15 * 60 + 30,    # 3:30 PM in minutes
        "duration": 15          # 15 minutes
    },
    "Joseph": {
        "location": "Presidio",
        "start": 7 * 60,        # 7:00 AM in minutes
        "end": 13 * 60,         # 1:00 PM in minutes
        "duration": 45          # 45 minutes
    },
    "Andrew": {
        "location": "Nob Hill",
        "start": 19 * 60 + 45,  # 7:45 PM in minutes
        "end": 22 * 60,         # 10:00 PM in minutes
        "duration": 105         # 105 minutes
    },
    "John": {
        "location": "The Castro",
        "start": 13 * 60 + 15,  # 1:15 PM in minutes
        "end": 19 * 60 + 45,    # 7:45 PM in minutes
        "duration": 45          # 45 minutes
    }
}

# Initialize Z3 solver
s = Solver()

# Create variables for each meeting: start time, end time, and whether the meeting is scheduled
meetings = {}
for name in friends:
    meetings[name] = {
        "start": Int(f"start_{name}"),
        "end": Int(f"end_{name}"),
        "scheduled": Bool(f"scheduled_{name}")
    }

# Current location starts at Embarcadero
current_location = "Embarcadero"
current_time = 9 * 60  # 9:00 AM in minutes

# Constraints for each meeting
for name, data in friends.items():
    meeting = meetings[name]
    s.add(Implies(meeting["scheduled"], meeting["start"] >= data["start"]))
    s.add(Implies(meeting["scheduled"], meeting["end"] <= data["end"]))
    s.add(Implies(meeting["scheduled"], meeting["end"] == meeting["start"] + data["duration"]))

# Order constraints: ensure meetings are scheduled in a feasible order
# We'll use a list to keep track of the order and enforce travel times
order = []
for name in friends:
    order.append((meetings[name]["start"], meetings[name]["end"], meetings[name]["scheduled"], name))

# Ensure that the first meeting is after the current time
for name in friends:
    s.add(Implies(meetings[name]["scheduled"], meetings[name]["start"] >= current_time + travel_times[current_location][friends[name]["location"]]))

# Ensure that subsequent meetings have enough travel time between them
for i in range(len(order)):
    for j in range(len(order)):
        if i != j:
            s.add(Implies(And(order[i][2], order[j][2], order[i][1] < order[j][0]),
                         order[j][0"] >= order[i][1"] + travel_times[friends[order[i][3]]["location"]][friends[order[j][3]]["location"]]))

# Maximize the number of meetings scheduled
s.maximize(Sum([If(meetings[name]["scheduled"], 1, 0) for name in friends]))

# Solve the problem
if s.check() == sat:
    m = s.model()
    itinerary = []
    for name in friends:
        if m.evaluate(meetings[name]["scheduled"]):
            start = m.evaluate(meetings[name]["start"])
            end = m.evaluate(meetings[name]["end"])
            start_time = f"{start.as_long() // 60:02d}:{start.as_long() % 60:02d}"
            end_time = f"{end.as_long() // 60:02d}:{end.as_long() % 60:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")