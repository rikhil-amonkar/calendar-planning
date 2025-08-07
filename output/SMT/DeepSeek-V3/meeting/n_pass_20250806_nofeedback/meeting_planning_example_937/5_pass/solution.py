from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver with a longer timeout
    s = Solver()
    s.set("timeout", 60000)  # 60 second timeout

    # Friend data with time windows in minutes since midnight
    friends = [
        {"name": "David", "location": "Sunset District", "start": 555, "end": 1320, "duration": 15},
        {"name": "Kenneth", "location": "Union Square", "start": 1275, "end": 1305, "duration": 15},
        {"name": "Patricia", "location": "Nob Hill", "start": 900, "end": 1155, "duration": 120},
        {"name": "Mary", "location": "Marina District", "start": 885, "end": 1005, "duration": 45},
        {"name": "Charles", "location": "Richmond District", "start": 1035, "end": 1260, "duration": 15},
        {"name": "Joshua", "location": "Financial District", "start": 870, "end": 1035, "duration": 90},
        {"name": "Ronald", "location": "Embarcadero", "start": 1095, "end": 1245, "duration": 30},
        {"name": "George", "location": "The Castro", "start": 855, "end": 1140, "duration": 105},
        {"name": "Kimberly", "location": "Alamo Square", "start": 540, "end": 870, "duration": 105},
        {"name": "William", "location": "Presidio", "start": 420, "end": 765, "duration": 60}
    ]

    # Travel times between locations (minutes)
    travel = {
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
    }

    # Sort friends by duration (longest first) and then by window size
    friends.sort(key=lambda x: (-x["duration"], x["end"] - x["start"]))

    # Create variables for meeting times
    vars = {}
    for f in friends:
        name = f["name"]
        vars[name] = {
            "start": Int(f"start_{name}"),
            "end": Int(f"end_{name}"),
            "location": f["location"]
        }

    # Base constraints for each meeting
    for f in friends:
        name = f["name"]
        s.add(vars[name]["start"] >= f["start"])
        s.add(vars[name]["end"] <= f["end"])
        s.add(vars[name]["end"] - vars[name]["start"] >= f["duration"])

    # Initial location and time
    current_loc = "Russian Hill"
    current_time = 540  # 9:00 AM

    # Schedule meetings in order of priority
    for f in friends:
        name = f["name"]
        loc = f["location"]
        
        # Add travel time constraint
        travel_time = travel.get((current_loc, loc), 0)
        s.add(vars[name]["start"] >= current_time + travel_time)
        
        # Update current time and location
        current_time = vars[name]["end"]
        current_loc = loc

    # Try to solve
    if s.check() == sat:
        model = s.model()
        schedule = []
        
        # Convert model to human-readable times
        for f in friends:
            name = f["name"]
            start = model[vars[name]["start"]].as_long()
            end = model[vars[name]["end"]].as_long()
            
            # Convert minutes to HH:MM format
            start_time = f"{start//60:02d}:{start%60:02d}"
            end_time = f"{end//60:02d}:{end%60:02d}"
            
            schedule.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time
            })
        
        return {"itinerary": schedule}
    else:
        # Provide more detailed error information
        unsat_core = s.unsat_core()
        return {
            "error": "No feasible schedule found",
            "unsat_core": str(unsat_core),
            "constraints": str(s)
        }

# Run the solver and print results
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))