import json
from z3 import *

def solve_scheduling_problem():
    # Initialize the solver
    solver = Solver()

    # Define the friends and their availability
    friends = {
        "Matthew": {"location": "Presidio", "start": 8*60 + 15, "end": 9*60, "duration": 15},
        "Richard": {"location": "Fisherman's Wharf", "start": 11*60, "end": 12*60 + 45, "duration": 60},
        "Elizabeth": {"location": "Nob Hill", "start": 11*60 + 45, "end": 18*60 + 30, "duration": 75},
        "Anthony": {"location": "Pacific Heights", "start": 14*60 + 15, "end": 16*60, "duration": 30},
        "Brian": {"location": "North Beach", "start": 13*60, "end": 19*60, "duration": 90},
        "Kenneth": {"location": "Chinatown", "start": 13*60 + 45, "end": 19*60 + 30, "duration": 105},
        "Ashley": {"location": "Haight-Ashbury", "start": 15*60, "end": 20*60 + 30, "duration": 90},
        "Kimberly": {"location": "Alamo Square", "start": 17*60 + 30, "end": 21*60 + 15, "duration": 45},
        "Deborah": {"location": "Union Square", "start": 17*60 + 30, "end": 22*60, "duration": 60},
        "Jessica": {"location": "Golden Gate Park", "start": 20*60, "end": 21*60 + 45, "duration": 105}
    }

    # Define travel times (simplified for this example)
    travel_times = {
        ("Bayview", "Presidio"): 32,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Pacific Heights", "North Beach"): 9,
        ("North Beach", "Chinatown"): 6,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Alamo Square", "Union Square"): 14,
        ("Union Square", "Golden Gate Park"): 22
    }

    # Create variables for each meeting
    meetings = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meetings[name] = {"start": start, "end": end, "location": friends[name]["location"]}
        # Constrain the meeting to be within the friend's availability
        solver.add(start >= friends[name]["start"])
        solver.add(end <= friends[name]["end"])
        solver.add(end == start + friends[name]["duration"])

    # Constrain the start time to be after arrival at Bayview (9:00 AM)
    solver.add(meetings["Matthew"]["start"] >= 9*60)

    # Define the sequence of meetings and add travel time constraints
    sequence = ["Matthew", "Richard", "Elizabeth", "Anthony", "Brian", "Kenneth", "Ashley", "Kimberly", "Deborah", "Jessica"]
    for i in range(len(sequence) - 1):
        current = sequence[i]
        next_ = sequence[i + 1]
        # Ensure the next meeting starts after the current meeting ends plus travel time
        solver.add(meetings[next_]["start"] >= meetings[current]["end"] + travel_times.get((friends[current]["location"], friends[next_]["location"]), 0))

    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for name in sequence:
            start = model[meetings[name]["start"]].as_long()
            end = model[meetings[name]["end"]].as_long()
            start_time = f"{start // 60:02d}:{start % 60:02d}"
            end_time = f"{end // 60:02d}:{end % 60:02d}"
            itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))