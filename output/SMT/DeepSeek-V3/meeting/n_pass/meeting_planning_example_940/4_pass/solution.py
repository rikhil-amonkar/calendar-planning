from z3 import *
import json
from itertools import combinations

def solve_scheduling():
    s = Optimize()

    # Friends data with locations, time windows, and required durations
    friends = {
        "Kevin": {"location": "Mission District", "start": 20*60+45, "end": 21*60+45, "duration": 60},
        "Mark": {"location": "Fisherman's Wharf", "start": 17*60+15, "end": 20*60+0, "duration": 90},
        "Jessica": {"location": "Russian Hill", "start": 9*60+0, "end": 15*60+0, "duration": 120},
        "Jason": {"location": "Marina District", "start": 15*60+15, "end": 21*60+45, "duration": 120},
        "John": {"location": "North Beach", "start": 9*60+45, "end": 18*60+0, "duration": 15},
        "Karen": {"location": "Chinatown", "start": 16*60+45, "end": 19*60+0, "duration": 75},
        "Sarah": {"location": "Pacific Heights", "start": 17*60+30, "end": 18*60+15, "duration": 45},
        "Amanda": {"location": "The Castro", "start": 20*60+0, "end": 21*60+15, "duration": 60},
        "Nancy": {"location": "Nob Hill", "start": 9*60+45, "end": 13*60+0, "duration": 45},
        "Rebecca": {"location": "Sunset District", "start": 8*60+45, "end": 15*60+0, "duration": 75}
    }

    # Travel times between locations (minutes)
    travel_times = {
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Sunset District"): 27,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Union Square"): 15,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Union Square"): 10,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Union Square"): 16,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Union Square"): 7,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Union Square"): 7,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Union Square"): 12,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Union Square"): 19,
        ("Nob Hill", "Union Square"): 7
    }

    # Add reverse directions
    reverse_times = {(b,a):t for (a,b),t in travel_times.items() if (b,a) not in travel_times}
    travel_times.update(reverse_times)

    # Create variables
    start_vars = {name: Int(f"start_{name}") for name in friends}
    meet_vars = {name: Bool(f"meet_{name}") for name in friends}

    # Basic constraints
    for name in friends:
        s.add(Implies(meet_vars[name], start_vars[name] >= friends[name]["start"]))
        s.add(Implies(meet_vars[name], start_vars[name] + friends[name]["duration"] <= friends[name]["end"]))
        s.add(Implies(Not(meet_vars[name]), start_vars[name] == -1))

    # No overlapping meetings with travel time
    for name1, name2 in combinations(friends.keys(), 2):
        loc1 = friends[name1]["location"]
        loc2 = friends[name2]["location"]
        travel = travel_times.get((loc1, loc2), 60)  # Default travel time
        
        constraint = Implies(
            And(meet_vars[name1], meet_vars[name2]),
            Or(
                start_vars[name1] + friends[name1]["duration"] + travel <= start_vars[name2],
                start_vars[name2] + friends[name2]["duration"] + travel <= start_vars[name1]
            )
        )
        s.add(constraint)

    # Must meet Kevin at his exact time window
    s.add(meet_vars["Kevin"])
    s.add(start_vars["Kevin"] == friends["Kevin"]["start"])

    # Maximize number of friends met
    s.maximize(Sum([If(meet_vars[name], 1, 0) for name in friends]))

    # Solve and format output
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in friends:
            if model.evaluate(meet_vars[name]):
                start = model.evaluate(start_vars[name]).as_long()
                end = start + friends[name]["duration"]
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start//60:02d}:{start%60:02d}",
                    "end_time": f"{end//60:02d}:{end%60:02d}"
                })
        itinerary.sort(key=lambda x: int(x["start_time"][:2])*60 + int(x["start_time"][3:]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))