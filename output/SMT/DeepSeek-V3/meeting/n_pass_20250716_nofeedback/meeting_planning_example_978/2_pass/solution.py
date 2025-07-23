from z3 import *
import json

def solve_scheduling_problem():
    s = Solver()

    # Define friends and their availability
    friends = {
        "Stephanie": {"location": "Fisherman's Wharf", "start": 15.5, "end": 22.0, "duration": 0.5},
        "Lisa": {"location": "Financial District", "start": 10.75, "end": 17.25, "duration": 0.25},
        "Melissa": {"location": "Russian Hill", "start": 17.0, "end": 21.75, "duration": 2.0},
        "Betty": {"location": "Marina District", "start": 10.75, "end": 14.25, "duration": 1.0},
        "Sarah": {"location": "Richmond District", "start": 16.25, "end": 19.5, "duration": 1.75},
        "Daniel": {"location": "Pacific Heights", "start": 18.5, "end": 21.75, "duration": 1.0},
        "Joshua": {"location": "Haight-Ashbury", "start": 9.0, "end": 15.5, "duration": 0.25},
        "Joseph": {"location": "Presidio", "start": 7.0, "end": 13.0, "duration": 0.75},
        "Andrew": {"location": "Nob Hill", "start": 19.75, "end": 22.0, "duration": 1.75},
        "John": {"location": "The Castro", "start": 13.25, "end": 19.75, "duration": 0.75}
    }

    # Travel times dictionary (simplified)
    travel_times = {
        ("Embarcadero", "Fisherman's Wharf"): 6/60,
        ("Embarcadero", "Financial District"): 5/60,
        ("Embarcadero", "Russian Hill"): 8/60,
        ("Embarcadero", "Marina District"): 12/60,
        ("Embarcadero", "Richmond District"): 21/60,
        ("Embarcadero", "Pacific Heights"): 11/60,
        ("Embarcadero", "Haight-Ashbury"): 21/60,
        ("Embarcadero", "Presidio"): 20/60,
        ("Embarcadero", "Nob Hill"): 10/60,
        ("Embarcadero", "The Castro"): 25/60,
        ("Fisherman's Wharf", "Financial District"): 11/60,
        ("Fisherman's Wharf", "Russian Hill"): 7/60,
        ("Fisherman's Wharf", "Marina District"): 9/60,
        ("Financial District", "Russian Hill"): 11/60,
        ("Financial District", "Marina District"): 15/60,
        ("Russian Hill", "Marina District"): 7/60,
        ("Russian Hill", "Richmond District"): 14/60,
        ("Russian Hill", "Pacific Heights"): 7/60,
        ("Marina District", "Richmond District"): 11/60,
        ("Marina District", "Pacific Heights"): 7/60,
        ("Richmond District", "Pacific Heights"): 10/60,
        ("Richmond District", "Haight-Ashbury"): 10/60,
        ("Pacific Heights", "Haight-Ashbury"): 11/60,
        ("Haight-Ashbury", "The Castro"): 6/60,
        ("Nob Hill", "Russian Hill"): 5/60,
        ("Nob Hill", "Pacific Heights"): 8/60,
        # Add more as needed
    }

    # Create variables for each meeting
    meeting_vars = {}
    for name in friends:
        start = Real(f'start_{name}')
        end = Real(f'end_{name}')
        meeting_vars[name] = (start, end)
        s.add(start >= friends[name]["start"])
        s.add(end <= friends[name]["end"])
        s.add(end == start + friends[name]["duration"])

    # Initial location and time
    current_time = 9.0
    current_location = "Embarcadero"

    # Define a possible order (this is a heuristic; a better approach would optimize the order)
    order = ["Joseph", "Joshua", "Betty", "Lisa", "John", "Sarah", "Melissa", "Daniel", "Andrew", "Stephanie"]

    # Add travel time constraints
    for i in range(len(order)):
        if i == 0:
            # First meeting: travel from Embarcadero to friend's location
            friend = order[i]
            location = friends[friend]["location"]
            travel_key = (current_location, location)
            if travel_key in travel_times:
                travel_time = travel_times[travel_key]
                s.add(meeting_vars[friend][0] >= current_time + travel_time)
            else:
                # If no direct travel time, assume some default (this is a simplification)
                s.add(meeting_vars[friend][0] >= current_time + 0.5)  # Default 30 mins
        else:
            # Subsequent meetings: travel from previous to current location
            prev_friend = order[i-1]
            prev_location = friends[prev_friend]["location"]
            friend = order[i]
            location = friends[friend]["location"]
            travel_key = (prev_location, location)
            if travel_key in travel_times:
                travel_time = travel_times[travel_key]
                s.add(meeting_vars[friend][0] >= meeting_vars[prev_friend][1] + travel_time)
            else:
                # If no direct travel time, assume some default
                s.add(meeting_vars[friend][0] >= meeting_vars[prev_friend][1] + 0.5)  # Default 30 mins

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order:
            start = model[meeting_vars[name][0]].as_fraction()
            end = model[meeting_vars[name][1]].as_fraction()
            start_time = float(start.numerator) / float(start.denominator)
            end_time = float(end.numerator) / float(end.denominator)
            # Convert to HH:MM format
            start_hh = int(start_time)
            start_mm = int((start_time - start_hh) * 60)
            end_hh = int(end_time)
            end_mm = int((end_time - end_hh) * 60)
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))