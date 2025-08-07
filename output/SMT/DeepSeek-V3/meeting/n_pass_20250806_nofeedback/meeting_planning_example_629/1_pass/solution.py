from z3 import *
import json

def solve_scheduling():
    # Define the travel times between locations (in minutes)
    travel_times = {
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Bayview"): 23,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Bayview"): 31,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Bayview"): 22,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Bayview"): 22,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Bayview"): 26,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Bayview"): 23,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Golden Gate Park"): 22,
    }

    # Define friends' availability and constraints
    friends = [
        {"name": "Matthew", "location": "Presidio", "start": (11, 0), "end": (21, 0), "duration": 90},
        {"name": "Margaret", "location": "Chinatown", "start": (9, 15), "end": (18, 45), "duration": 90},
        {"name": "Nancy", "location": "Pacific Heights", "start": (14, 15), "end": (17, 0), "duration": 15},
        {"name": "Helen", "location": "Richmond District", "start": (19, 45), "end": (22, 0), "duration": 60},
        {"name": "Rebecca", "location": "Fisherman's Wharf", "start": (21, 15), "end": (22, 15), "duration": 60},
        {"name": "Kimberly", "location": "Golden Gate Park", "start": (13, 0), "end": (16, 30), "duration": 120},
        {"name": "Kenneth", "location": "Bayview", "start": (14, 30), "end": (18, 0), "duration": 60},
    ]

    # Initialize Z3 solver
    solver = Solver()

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(m):
        total = m + 540
        h = total // 60
        m = total % 60
        return f"{h:02d}:{m:02d}"

    # Create variables for each meeting's start and end times
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "duration": friend["duration"],
            "available_start": time_to_minutes(*friend["start"]),
            "available_end": time_to_minutes(*friend["end"]),
        })

    # Add constraints for each meeting
    for meeting in meetings:
        solver.add(meeting["start"] >= meeting["available_start"])
        solver.add(meeting["end"] <= meeting["available_end"])
        solver.add(meeting["end"] == meeting["start"] + meeting["duration"])

    # Add constraints for travel times between consecutive meetings
    for i in range(len(meetings)):
        for j in range(len(meetings)):
            if i != j:
                # Ensure no overlap and travel time is accounted for
                loc_i = meetings[i]["location"]
                loc_j = meetings[j]["location"]
                travel_time = travel_times.get((loc_i, loc_j), 0)
                solver.add(Or(
                    meetings[j]["start"] >= meetings[i]["end"] + travel_time,
                    meetings[i]["start"] >= meetings[j]["end"] + travel_time
                ))

    # Ensure the first meeting starts after arrival at Russian Hill (9:00 AM)
    solver.add(And([meeting["start"] >= 0 for meeting in meetings]))

    # Try to maximize the number of friends met (all in this case)
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for meeting in meetings:
            start = model[meeting["start"]].as_long()
            end = model[meeting["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end),
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))