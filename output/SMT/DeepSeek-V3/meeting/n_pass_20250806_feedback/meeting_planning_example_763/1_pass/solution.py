from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the locations and their travel times
    locations = [
        "Chinatown",
        "Embarcadero",
        "Pacific Heights",
        "Russian Hill",
        "Haight-Ashbury",
        "Golden Gate Park",
        "Fisherman's Wharf",
        "Sunset District",
        "The Castro"
    ]

    # Travel times matrix (from_location, to_location) -> minutes
    travel_times = {
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "The Castro"): 22,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "The Castro"): 25,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "The Castro"): 16,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "The Castro"): 13,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "The Castro"): 17,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Sunset District"): 17
    }

    # Friends and their availability
    friends = [
        {"name": "Richard", "location": "Embarcadero", "start": (15, 15), "end": (18, 45), "duration": 90},
        {"name": "Mark", "location": "Pacific Heights", "start": (15, 0), "end": (17, 0), "duration": 45},
        {"name": "Matthew", "location": "Russian Hill", "start": (17, 30), "end": (21, 0), "duration": 90},
        {"name": "Rebecca", "location": "Haight-Ashbury", "start": (14, 45), "end": (18, 0), "duration": 60},
        {"name": "Melissa", "location": "Golden Gate Park", "start": (13, 45), "end": (17, 30), "duration": 90},
        {"name": "Margaret", "location": "Fisherman's Wharf", "start": (14, 45), "end": (20, 15), "duration": 15},
        {"name": "Emily", "location": "Sunset District", "start": (15, 45), "end": (17, 0), "duration": 45},
        {"name": "George", "location": "The Castro", "start": (14, 0), "end": (16, 15), "duration": 75}
    ]

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(m):
        total = 540 + m
        h = total // 60
        m = total % 60
        return f"{h:02d}:{m:02d}"

    # Create variables for each friend's meeting start and end times
    meet_vars = []
    for friend in friends:
        start_min = time_to_minutes(*friend["start"])
        end_min = time_to_minutes(*friend["end"])
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        s.add(start >= start_min)
        s.add(end <= end_min)
        s.add(end - start >= friend["duration"])
        meet_vars.append((friend, start, end))

    # Add constraints for travel times between consecutive meetings
    for i in range(len(meet_vars)):
        for j in range(len(meet_vars)):
            if i != j:
                friend1, start1, end1 = meet_vars[i]
                friend2, start2, end2 = meet_vars[j]
                travel_time = travel_times.get((friend1["location"], friend2["location"]), 0)
                s.add(Or(
                    start2 >= end1 + travel_time,  # friend2 after friend1
                    start1 >= end2 + travel_time   # friend1 after friend2
                ))

    # Maximize the number of friends met (soft constraint)
    met = [Bool(f"met_{friend['name']}") for friend in friends]
    for i, (friend, start, end) in enumerate(meet_vars):
        s.add(Implies(met[i], end - start >= friend["duration"]))

    # Optimize to meet as many friends as possible
    opt = Optimize()
    for m in met:
        opt.add_soft(m)
    opt.add(s)

    # Solve the problem
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for friend, start, end in meet_vars:
            if model.evaluate(met[friends.index(friend)]):
                start_time = model.evaluate(start).as_long()
                end_time = model.evaluate(end).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))