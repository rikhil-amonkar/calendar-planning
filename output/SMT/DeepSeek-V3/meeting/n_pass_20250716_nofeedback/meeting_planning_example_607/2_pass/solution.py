from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = [
        {"name": "Karen", "location": "Russian Hill", "start": (20, 45), "end": (21, 45), "min_duration": 60},
        {"name": "Jessica", "location": "The Castro", "start": (15, 45), "end": (19, 30), "min_duration": 60},
        {"name": "Matthew", "location": "Richmond District", "start": (7, 30), "end": (15, 15), "min_duration": 15},
        {"name": "Michelle", "location": "Marina District", "start": (10, 30), "end": (18, 45), "min_duration": 75},
        {"name": "Carol", "location": "North Beach", "start": (12, 0), "end": (17, 0), "min_duration": 90},
        {"name": "Stephanie", "location": "Union Square", "start": (10, 45), "end": (14, 15), "min_duration": 30},
        {"name": "Linda", "location": "Golden Gate Park", "start": (10, 45), "end": (22, 0), "min_duration": 90}
    ]

    # Current location starts at Sunset District at 9:00 AM (540 minutes since midnight)
    current_time = 540  # 9:00 AM in minutes

    # Create variables for each friend's meeting start and end times (in minutes since midnight)
    variables = {}
    for friend in friends:
        name = friend["name"]
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        variables[name] = (start_var, end_var)

    # Add constraints for each friend's meeting
    for friend in friends:
        name = friend["name"]
        start_var, end_var = variables[name]
        friend_start = friend["start"][0] * 60 + friend["start"][1]
        friend_end = friend["end"][0] * 60 + friend["end"][1]
        min_duration = friend["min_duration"]

        # Meeting must start and end within friend's availability
        s.add(start_var >= friend_start)
        s.add(end_var <= friend_end)
        # Meeting duration must be at least min_duration
        s.add(end_var - start_var >= min_duration)

    # Define travel times between locations
    travel_times = {
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "North Beach"): 29,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Union Square"): 11,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Golden Gate Park"): 11,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Golden Gate Park"): 18,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "The Castro"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Golden Gate Park"): 22,
        ("Union Square", "Sunset District"): 26,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "The Castro"): 19,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Golden Gate Park"): 22,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Union Square"): 22,
    }

    # Define the order of meetings (heuristic based on end times)
    order = ["Matthew", "Michelle", "Stephanie", "Carol", "Jessica", "Linda", "Karen"]

    # Initialize current time and location
    current_location = "Sunset District"
    current_time_var = current_time

    # Add constraints for travel times between meetings
    for name in order:
        friend = next(f for f in friends if f["name"] == name)
        start_var, end_var = variables[name]
        location = friend["location"]

        # Travel time from current_location to friend's location
        travel_time = travel_times.get((current_location, location), 0)
        if (current_location, location) not in travel_times:
            travel_time = travel_times.get((location, current_location), 0)

        # The meeting must start after current_time_var + travel_time
        s.add(start_var >= current_time_var + travel_time)

        # Update current_time_var and current_location
        current_time_var = end_var
        current_location = location

    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        final_itinerary = []
        for name in order:
            start_var, end_var = variables[name]
            start_val = model.evaluate(start_var).as_long()
            end_val = model.evaluate(end_var).as_long()
            final_itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_val // 60:02d}:{start_val % 60:02d}",
                "end_time": f"{end_val // 60:02d}:{end_val % 60:02d}"
            })
        return {"itinerary": final_itinerary}
    else:
        return {"itinerary": []}

# Run the solver
solution = solve_scheduling()
print(json.dumps(solution, indent=2))