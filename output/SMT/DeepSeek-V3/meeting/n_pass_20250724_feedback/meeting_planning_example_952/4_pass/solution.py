import json
from z3 import *

def solve_scheduling_problem():
    # Initialize solver
    solver = Solver()

    # Define friends and their availability
    friends = {
        "Matthew": {"location": "Presidio", "start": 8*60+15, "end": 9*60, "duration": 15},
        "Richard": {"location": "Fisherman's Wharf", "start": 11*60, "end": 12*60+45, "duration": 60},
        "Elizabeth": {"location": "Nob Hill", "start": 11*60+45, "end": 18*60+30, "duration": 75},
        "Anthony": {"location": "Pacific Heights", "start": 14*60+15, "end": 16*60, "duration": 30},
        "Brian": {"location": "North Beach", "start": 13*60, "end": 19*60, "duration": 90},
        "Kenneth": {"location": "Chinatown", "start": 13*60+45, "end": 19*60+30, "duration": 105},
        "Ashley": {"location": "Haight-Ashbury", "start": 15*60, "end": 20*60+30, "duration": 90},
        "Kimberly": {"location": "Alamo Square", "start": 17*60+30, "end": 21*60+15, "duration": 45},
        "Deborah": {"location": "Union Square", "start": 17*60+30, "end": 22*60, "duration": 60},
        "Jessica": {"location": "Golden Gate Park", "start": 20*60, "end": 21*60+45, "duration": 105}
    }

    # Define all travel times (from the problem statement)
    travel_times = {
        ("Bayview", "North Beach"): 22,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Pacific Heights"): 23,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Pacific Heights"): 8,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Pacific Heights"): 15,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Pacific Heights"): 11,
        ("Chinatown", "Pacific Heights"): 10
    }

    # Create variables for each meeting
    meetings = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meetings[name] = {"start": start, "end": end, "location": friends[name]["location"]}
        # Constrain meeting times
        solver.add(start >= friends[name]["start"])
        solver.add(end <= friends[name]["end"])
        solver.add(end == start + friends[name]["duration"])

    # Constrain start time after arrival at Bayview (9:00 AM)
    solver.add(meetings["Matthew"]["start"] >= 9*60)

    # Create a list of all friends except Matthew (handled separately)
    friend_names = [name for name in friends if name != "Matthew"]
    n = len(friend_names)

    # Create variables to represent the order of meetings
    order = [Int(f"order_{i}") for i in range(n)]
    # Each order variable must be between 0 and n-1
    for o in order:
        solver.add(o >= 0, o < n)
    # All order variables must be distinct
    solver.add(Distinct(order))

    # Create variables for the start location of each meeting
    # First meeting starts from Bayview (after Matthew)
    prev_location = "Bayview"
    prev_end = meetings["Matthew"]["end"]

    # Add constraints for the sequence of meetings
    for i in range(n):
        current_friend = friend_names[order[i]]
        current_meeting = meetings[current_friend]
        
        # Get travel time from previous location
        travel_time = travel_times.get((prev_location, current_meeting["location"]), 0)
        
        # Current meeting must start after previous meeting ends plus travel time
        solver.add(current_meeting["start"] >= prev_end + travel_time)
        
        # Update for next iteration
        prev_location = current_meeting["location"]
        prev_end = current_meeting["end"]

    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        # Get the order of meetings
        meeting_order = ["Matthew"] + [friend_names[model[o].as_long()] for o in order]
        itinerary = []
        for name in meeting_order:
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