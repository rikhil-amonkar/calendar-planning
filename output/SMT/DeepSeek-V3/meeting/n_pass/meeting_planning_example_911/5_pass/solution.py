from z3 import *
import json

def solve_scheduling():
    s = Solver()

    # Friend data with adjusted priorities
    friends = [
        {"name": "Nancy", "location": "Nob Hill", "start": 8*60+15, "end": 12*60+45, "duration": 90, "priority": 1},
        {"name": "Stephanie", "location": "Haight-Ashbury", "start": 10*60+15, "end": 12*60+15, "duration": 75, "priority": 2},
        {"name": "David", "location": "Marina District", "start": 11*60+15, "end": 13*60+15, "duration": 120, "priority": 3},
        {"name": "Elizabeth", "location": "Union Square", "start": 11*60+30, "end": 21*60+0, "duration": 60, "priority": 4},
        {"name": "Robert", "location": "Financial District", "start": 13*60+15, "end": 15*60+15, "duration": 45, "priority": 5},
        {"name": "Brian", "location": "Embarcadero", "start": 14*60+15, "end": 16*60+0, "duration": 105, "priority": 6},
        {"name": "James", "location": "Presidio", "start": 15*60+0, "end": 18*60+15, "duration": 120, "priority": 7},
        {"name": "Melissa", "location": "Richmond District", "start": 14*60+0, "end": 19*60+30, "duration": 30, "priority": 8},
        {"name": "Sarah", "location": "Golden Gate Park", "start": 17*60+0, "end": 19*60+15, "duration": 75, "priority": 9},
        {"name": "Steven", "location": "North Beach", "start": 17*60+30, "end": 20*60+30, "duration": 15, "priority": 10}
    ]

    # Travel times (simplified for this example)
    travel_times = {
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "North Beach"): 20,
        # Add more travel times as needed
    }

    # Create variables
    variables = {}
    for friend in friends:
        name = friend["name"]
        variables[name] = {
            "start": Int(f'start_{name}'),
            "end": Int(f'end_{name}'),
            "met": Bool(f'met_{name}')
        }

    # Starting point
    current_time = 0
    current_location = "The Castro"

    # Process friends in priority order
    for friend in sorted(friends, key=lambda x: x["priority"]):
        name = friend["name"]
        loc = friend["location"]
        duration = friend["duration"]
        
        # Travel time from current location
        travel = travel_times.get((current_location, loc), 30)  # Default 30 min if not specified
        
        # Meeting must start after arrival
        s.add(Implies(variables[name]["met"], variables[name]["start"] >= current_time + travel))
        
        # Meeting must end before friend's availability ends
        s.add(Implies(variables[name]["met"], variables[name]["end"] <= friend["end"] - 9*60))
        
        # Meeting duration
        s.add(Implies(variables[name]["met"], variables[name]["end"] - variables[name]["start"] >= duration))
        
        # If we meet this friend, update current time and location
        current_time = If(variables[name]["met"], variables[name]["end"], current_time)
        current_location = If(variables[name]["met"], loc, current_location)

    # Try to maximize number of meetings
    s.maximize(Sum([If(variables[f["name"]]["met"], 1, 0) for f in friends]))

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for friend in friends:
            name = friend["name"]
            if m.evaluate(variables[name]["met"]):
                start = m[variables[name]["start"]].as_long()
                end = m[variables[name]["end"]].as_long()
                start_time = f"{(start + 9*60) // 60:02d}:{(start + 9*60) % 60:02d}"
                end_time = f"{(end + 9*60) // 60:02d}:{(end + 9*60) % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        return {"itinerary": sorted(itinerary, key=lambda x: x["start_time"])}
    else:
        return {"error": "No feasible schedule found"}

result = solve_scheduling()
print(json.dumps(result, indent=2))