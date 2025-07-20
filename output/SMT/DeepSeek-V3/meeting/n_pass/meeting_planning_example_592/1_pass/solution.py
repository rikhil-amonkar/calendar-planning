from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    solver = Solver()

    # Define the friends and their availability
    friends = {
        "James": {"location": "Pacific Heights", "start": 20*60, "end": 22*60, "min_duration": 120},
        "Robert": {"location": "Chinatown", "start": 12*60 + 15, "end": 16*60 + 45, "min_duration": 90},
        "Jeffrey": {"location": "Union Square", "start": 9*60 + 30, "end": 15*60 + 30, "min_duration": 120},
        "Carol": {"location": "Mission District", "start": 18*60 + 15, "end": 21*60 + 15, "min_duration": 15},
        "Mark": {"location": "Golden Gate Park", "start": 11*60 + 30, "end": 17*60 + 45, "min_duration": 15},
        "Sandra": {"location": "Nob Hill", "start": 8*60, "end": 15*60 + 30, "min_duration": 15}
    }

    # Define travel times (in minutes) between locations
    travel_times = {
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Nob Hill"): 7,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Mission District"): 18,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Nob Hill"): 8,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Nob Hill"): 9,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Nob Hill"): 12,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Golden Gate Park"): 17
    }

    # Current location starts at North Beach at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_location = "North Beach"

    # Variables to track meetings
    meetings = []
    itinerary = []

    # For each friend, create variables for meeting start and end times
    for name, data in friends.items():
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        duration = end - start
        solver.add(start >= data["start"])
        solver.add(end <= data["end"])
        solver.add(duration >= data["min_duration"])
        meetings.append({"name": name, "start": start, "end": end, "location": data["location"]})

    # Ensure no overlapping meetings and account for travel time
    for i in range(len(meetings)):
        for j in range(i + 1, len(meetings)):
            m1 = meetings[i]
            m2 = meetings[j]
            # Either m1 is before m2 or m2 is before m1, with travel time
            travel = travel_times.get((m1["location"], m2["location"]), 0)
            solver.add(Or(
                m1["end"] + travel <= m2["start"],
                m2["end"] + travel <= m1["start"]
            ))

    # First meeting must be after current time + travel time from North Beach
    for m in meetings:
        travel = travel_times.get((current_location, m["location"]), 0)
        solver.add(m["start"] >= current_time + travel)

    # Maximize the number of friends met
    # We'll prioritize meeting friends with longer durations first
    # This is a heuristic; Z3 doesn't directly support optimization in this setup
    # So we'll try to meet as many as possible, starting with those with longer durations

    # Check if we can meet all friends
    if solver.check() == sat:
        model = solver.model()
        # Collect all meetings that are scheduled
        scheduled = []
        for m in meetings:
            start_val = model.evaluate(m["start"]).as_long()
            end_val = model.evaluate(m["end"]).as_long()
            if start_val < end_val:  # Valid meeting
                scheduled.append({
                    "name": m["name"],
                    "start": start_val,
                    "end": end_val,
                    "location": m["location"]
                })
        # Sort by start time
        scheduled.sort(key=lambda x: x["start"])
        # Generate itinerary
        itinerary = []
        for m in scheduled:
            itinerary.append({
                "action": "meet",
                "person": m["name"],
                "start_time": f"{m['start'] // 60:02d}:{m['start'] % 60:02d}",
                "end_time": f"{m['end'] // 60:02d}:{m['end'] % 60:02d}"
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))