from z3 import *
import json

def solve_scheduling_problem():
    s = Optimize()

    # Define locations and travel times (in minutes)
    locations = ["Union Square", "Presidio", "Alamo Square", "Marina District", 
                "Financial District", "Nob Hill", "Sunset District", "Chinatown",
                "Russian Hill", "North Beach", "Haight-Ashbury"]

    travel_times = {
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Haight-Ashbury"): 18,
        # Add all other travel times similarly...
    }

    # Friends data with their constraints
    friends = [
        {"name": "Kimberly", "location": "Presidio", "start": (15, 30), "end": (16, 0), "duration": 15},
        {"name": "Elizabeth", "location": "Alamo Square", "start": (19, 15), "end": (20, 15), "duration": 15},
        {"name": "Joshua", "location": "Marina District", "start": (10, 30), "end": (14, 15), "duration": 45},
        {"name": "Sandra", "location": "Financial District", "start": (19, 30), "end": (20, 15), "duration": 45},
        {"name": "Kenneth", "location": "Nob Hill", "start": (12, 45), "end": (21, 45), "duration": 30},
        {"name": "Betty", "location": "Sunset District", "start": (14, 0), "end": (19, 0), "duration": 60},
        {"name": "Deborah", "location": "Chinatown", "start": (17, 15), "end": (20, 30), "duration": 15},
        {"name": "Barbara", "location": "Russian Hill", "start": (17, 30), "end": (21, 15), "duration": 120},
        {"name": "Steven", "location": "North Beach", "start": (17, 45), "end": (20, 45), "duration": 90},
        {"name": "Daniel", "location": "Haight-Ashbury", "start": (18, 30), "end": (18, 45), "duration": 15},
    ]

    # Convert times to minutes since 9:00 AM (540 minutes)
    for friend in friends:
        friend["start_min"] = friend["start"][0] * 60 + friend["start"][1] - 540
        friend["end_min"] = friend["end"][0] * 60 + friend["end"][1] - 540

    # Create Z3 variables
    for friend in friends:
        friend["z3_start"] = Int(f"{friend['name']}_start")
        friend["z3_end"] = Int(f"{friend['name']}_end")
        s.add(friend["z3_start"] >= friend["start_min"])
        s.add(friend["z3_end"] <= friend["end_min"])
        s.add(friend["z3_end"] - friend["z3_start"] >= friend["duration"])

    # Add travel time constraints
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            travel_time = travel_times.get((friends[i]["location"], friends[j]["location"]), 0)
            s.add(Or(
                friends[i]["z3_end"] + travel_time <= friends[j]["z3_start"],
                friends[j]["z3_end"] + travel_time <= friends[i]["z3_start"]
            ))

    # Try to maximize the number of meetings
    meet_counts = [If(friends[i]["z3_end"] > friends[i]["z3_start"], 1, 0) for i in range(len(friends))]
    s.maximize(Sum(meet_counts))

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for friend in friends:
            start = m.evaluate(friend["z3_start"]).as_long()
            end = m.evaluate(friend["z3_end"]).as_long()
            if start >= 0 and end > start:
                start_hour = (start + 540) // 60
                start_min = (start + 540) % 60
                end_hour = (end + 540) // 60
                end_min = (end + 540) % 60
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": f"{start_hour:02d}:{start_min:02d}",
                    "end_time": f"{end_hour:02d}:{end_min:02d}"
                })
        return {"itinerary": sorted(itinerary, key=lambda x: x["start_time"])}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))