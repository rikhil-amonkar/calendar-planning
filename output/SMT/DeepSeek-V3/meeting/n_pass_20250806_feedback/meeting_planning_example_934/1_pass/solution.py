import json
from z3 import *

def solve_scheduling_problem():
    # Initialize Z3 solver
    solver = Solver()

    # Define friends and their details
    friends = {
        "Mary": {"location": "Embarcadero", "start": 20*60, "end": 21*60 + 15, "min_duration": 75},
        "Kenneth": {"location": "The Castro", "start": 11*60 + 15, "end": 19*60 + 15, "min_duration": 30},
        "Joseph": {"location": "Haight-Ashbury", "start": 20*60, "end": 22*60, "min_duration": 120},
        "Sarah": {"location": "Union Square", "start": 11*60 + 45, "end": 14*60 + 30, "min_duration": 90},
        "Thomas": {"location": "North Beach", "start": 19*60 + 15, "end": 19*60 + 45, "min_duration": 15},
        "Daniel": {"location": "Pacific Heights", "start": 13*60 + 45, "end": 20*60 + 30, "min_duration": 15},
        "Richard": {"location": "Chinatown", "start": 8*60, "end": 18*60 + 45, "min_duration": 30},
        "Mark": {"location": "Golden Gate Park", "start": 17*60 + 30, "end": 21*60 + 30, "min_duration": 120},
        "David": {"location": "Marina District", "start": 20*60, "end": 21*60, "min_duration": 60},
        "Karen": {"location": "Russian Hill", "start": 13*60 + 15, "end": 18*60 + 30, "min_duration": 120}
    }

    # Define travel times (in minutes) between locations
    travel_times = {
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Russian Hill"): 5,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Russian Hill"): 8,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Russian Hill"): 18,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Russian Hill"): 13,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Russian Hill"): 4,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Russian Hill"): 7,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Russian Hill"): 8,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Marina District"): 7
    }

    # Create variables for each friend's meeting start and end times (in minutes since 9:00 AM)
    start_vars = {}
    end_vars = {}
    for name in friends:
        start_vars[name] = Int(f'start_{name}')
        end_vars[name] = Int(f'end_{name}')

    # Current location starts at Nob Hill at time 0 (9:00 AM)
    current_location = "Nob Hill"
    current_time = 0

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        solver.add(start_vars[name] >= friend["start"] - 9*60)  # Convert to minutes since 9:00 AM
        solver.add(end_vars[name] <= friend["end"] - 9*60)
        solver.add(end_vars[name] >= start_vars[name] + friend["min_duration"])

    # Define the order of meetings (this is a simplification; in reality, we need to model the sequence)
    # To model the sequence, we can use a list of booleans indicating whether a meeting is before another
    # This is complex; instead, we'll prioritize meeting as many friends as possible and let Z3 find a feasible order

    # To simplify, we'll assume the order is handled by the solver by adding constraints for travel times between consecutive meetings
    # This is a heuristic and may not cover all cases, but it's a starting point

    # We'll also need to ensure that meetings don't overlap and travel times are respected
    # This requires a more sophisticated model, possibly using a sequence of meetings with variables for order

    # For the sake of this example, let's prioritize meeting friends with tighter time windows first
    # and add constraints that ensure travel times are respected between consecutive meetings

    # Define a list of friends in order of priority (based on time windows)
    priority_order = ["Sarah", "Kenneth", "Karen", "Daniel", "Richard", "Mark", "Thomas", "Mary", "David", "Joseph"]

    # Create a list of all possible meetings
    meetings = []
    for name in priority_order:
        meetings.append((name, friends[name]["location"], start_vars[name], end_vars[name]))

    # Add constraints to ensure no overlapping meetings and travel times are respected
    for i in range(len(meetings)):
        for j in range(i + 1, len(meetings)):
            name1, loc1, start1, end1 = meetings[i]
            name2, loc2, start2, end2 = meetings[j]
            # Either meeting1 is before meeting2 with travel time, or vice versa
            travel_time = travel_times.get((loc1, loc2), 0)
            solver.add(Or(
                end1 + travel_time <= start2,
                end2 + travel_times.get((loc2, loc1), 0) <= start1
            ))

    # Ensure that the first meeting starts after current_time (0, since we start at 9:00 AM)
    for name in start_vars:
        solver.add(start_vars[name] >= 0)

    # To maximize the number of friends met, we can use a soft constraint or optimize
    # Here, we'll just check satisfiability and return the first feasible solution

    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for name in friends:
            if model[start_vars[name]] is not None and model[end_vars[name]] is not None:
                start = model[start_vars[name]].as_long()
                end = model[end_vars[name]].as_long()
                start_hour = (start + 9*60) // 60
                start_minute = (start + 9*60) % 60
                end_hour = (end + 9*60) // 60
                end_minute = (end + 9*60) % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_hour:02d}:{start_minute:02d}",
                    "end_time": f"{end_hour:02d}:{end_minute:02d}"
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))