from z3 import *
import json
from itertools import combinations

def solve_scheduling_problem():
    s = Solver()
    s.set("timeout", 30000)  # 30 second timeout

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

    # Complete travel times dictionary
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

    # Generate a reasonable meeting order based on earliest availability
    ordered_friends = sorted(friends.keys(), key=lambda x: friends[x]["start"])

    # Add travel time constraints
    prev_location = current_location
    prev_end = current_time
    for name in ordered_friends:
        location = friends[name]["location"]
        travel_key = (prev_location, location)
        
        # Find the fastest route (direct or via Embarcadero)
        direct_time = travel_times.get(travel_key, float('inf'))
        via_emb_time = travel_times.get((prev_location, "Embarcadero"), float('inf')) + \
                      travel_times.get(("Embarcadero", location), float('inf'))
        travel_time = min(direct_time, via_emb_time)
        
        if travel_time == float('inf'):
            travel_time = 0.5  # Default 30 minutes if no route found
        
        s.add(meeting_vars[name][0] >= prev_end + travel_time)
        prev_location = location
        prev_end = meeting_vars[name][1]

    # Add constraints to prevent overlapping meetings at same location
    locations = {f["location"] for f in friends.values()}
    for loc in locations:
        loc_meetings = [name for name in friends if friends[name]["location"] == loc]
        for m1, m2 in combinations(loc_meetings, 2):
            s.add(Or(
                meeting_vars[m1][1] <= meeting_vars[m2][0],
                meeting_vars[m2][1] <= meeting_vars[m1][0]
            ))

    # Try to solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in ordered_friends:
            start_val = model[meeting_vars[name][0]]
            end_val = model[meeting_vars[name][1]]
            
            # Handle Z3 numeric values
            def to_float(v):
                if is_rational_value(v):
                    return float(v.numerator_as_long())/float(v.denominator_as_long())
                elif is_algebraic_value(v):
                    return float(v.approx(10).as_fraction())
                return float(v.as_fraction())
            
            start_time = to_float(start_val)
            end_time = to_float(end_val)
            
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