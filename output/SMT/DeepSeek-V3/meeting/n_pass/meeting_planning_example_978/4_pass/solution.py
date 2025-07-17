from z3 import *
import json
from itertools import permutations
import time

def solve_scheduling_problem():
    # Initialize solver with timeout
    s = Solver()
    s.set("timeout", 60000)  # 60 second timeout

    # Define friends and their availability
    friends = {
        "Stephanie": {"location": "Fisherman's Wharf", "start": 15.5, "end": 22.0, "duration": 0.5, "priority": 1},
        "Lisa": {"location": "Financial District", "start": 10.75, "end": 17.25, "duration": 0.25, "priority": 2},
        "Melissa": {"location": "Russian Hill", "start": 17.0, "end": 21.75, "duration": 2.0, "priority": 3},
        "Betty": {"location": "Marina District", "start": 10.75, "end": 14.25, "duration": 1.0, "priority": 4},
        "Sarah": {"location": "Richmond District", "start": 16.25, "end": 19.5, "duration": 1.75, "priority": 5},
        "Daniel": {"location": "Pacific Heights", "start": 18.5, "end": 21.75, "duration": 1.0, "priority": 6},
        "Joshua": {"location": "Haight-Ashbury", "start": 9.0, "end": 15.5, "duration": 0.25, "priority": 7},
        "Joseph": {"location": "Presidio", "start": 7.0, "end": 13.0, "duration": 0.75, "priority": 8},
        "Andrew": {"location": "Nob Hill", "start": 19.75, "end": 22.0, "duration": 1.75, "priority": 9},
        "John": {"location": "The Castro", "start": 13.25, "end": 19.75, "duration": 0.75, "priority": 10}
    }

    # Travel times dictionary (complete)
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
        ("Presidio", "Embarcadero"): 20/60,
        ("Presidio", "Fisherman's Wharf"): 19/60,
        ("Presidio", "Financial District"): 23/60,
        ("Presidio", "Russian Hill"): 14/60,
        ("Presidio", "Marina District"): 11/60,
        ("Presidio", "Richmond District"): 7/60,
        ("Presidio", "Pacific Heights"): 11/60,
        ("Presidio", "Haight-Ashbury"): 15/60,
        ("Presidio", "Nob Hill"): 18/60,
        ("Presidio", "The Castro"): 21/60,
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

    # Priority-based ordering (earliest deadline first)
    ordered_friends = sorted(friends.keys(), 
                           key=lambda x: (friends[x]["end"], friends[x]["priority"]))

    # Try priority-based order first
    for attempt in [ordered_friends]:
        temp_solver = Solver()
        temp_solver.set("timeout", 30000)  # 30 second timeout per attempt
        
        # Add all constraints
        for name in friends:
            start, end = meeting_vars[name]
            temp_solver.add(start >= friends[name]["start"])
            temp_solver.add(end <= friends[name]["end"])
            temp_solver.add(end == start + friends[name]["duration"])

        # Add travel constraints
        prev_location = current_location
        prev_end = current_time
        for name in attempt:
            location = friends[name]["location"]
            travel_key = (prev_location, location)
            if travel_key in travel_times:
                travel_time = travel_times[travel_key]
                temp_solver.add(meeting_vars[name][0] >= prev_end + travel_time)
            else:
                # If no direct route, assume travel through Embarcadero
                to_emb = travel_times.get((prev_location, "Embarcadero"), 0.5)
                from_emb = travel_times.get(("Embarcadero", location), 0.5)
                temp_solver.add(meeting_vars[name][0] >= prev_end + to_emb + from_emb)
            prev_location = location
            prev_end = meeting_vars[name][1]

        # Try to solve
        start_time = time.time()
        if temp_solver.check() == sat:
            model = temp_solver.model()
            itinerary = []
            for name in attempt:
                start_val = model[meeting_vars[name][0]]
                end_val = model[meeting_vars[name][1]]
                
                # Handle Z3 numeric values
                if is_algebraic_value(start_val):
                    start_time = float(start_val.approx(10).as_fraction())
                    end_time = float(end_val.approx(10).as_fraction())
                else:
                    start_time = float(start_val.as_fraction())
                    end_time = float(end_val.as_fraction())
                
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
        elif time.time() - start_time > 29:
            continue  # Try next ordering if timeout

    return {"error": "No feasible schedule found within time limit"}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))