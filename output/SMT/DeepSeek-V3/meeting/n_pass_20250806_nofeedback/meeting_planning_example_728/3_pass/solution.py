from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define friends and their details
    friends = {
        "Karen": {"location": "Mission District", "start": "14:15", "end": "22:00", "min_duration": 30},
        "Richard": {"location": "Fisherman's Wharf", "start": "14:30", "end": "17:30", "min_duration": 30},
        "Robert": {"location": "Presidio", "start": "21:45", "end": "22:45", "min_duration": 60},
        "Joseph": {"location": "Union Square", "start": "11:45", "end": "14:45", "min_duration": 120},
        "Helen": {"location": "Sunset District", "start": "14:45", "end": "20:45", "min_duration": 105},
        "Elizabeth": {"location": "Financial District", "start": "10:00", "end": "12:45", "min_duration": 75},
        "Kimberly": {"location": "Haight-Ashbury", "start": "14:15", "end": "17:30", "min_duration": 105},
        "Ashley": {"location": "Russian Hill", "start": "11:30", "end": "21:30", "min_duration": 45}
    }

    # Travel times dictionary (simplified for access)
    travel_times = {
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Russian Hill"): 8,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Russian Hill"): 15,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Russian Hill"): 14,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Russian Hill"): 13,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Russian Hill"): 24,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Russian Hill"): 11,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Haight-Ashbury"): 17
    }

    # Helper function to convert time string to minutes
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert friend availability to minutes
    for name in friends:
        friends[name]["start_min"] = time_to_minutes(friends[name]["start"])
        friends[name]["end_min"] = time_to_minutes(friends[name]["end"])

    # Current location starts at Marina District at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Marina District"

    # Define variables for each meeting: start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meeting_vars[name] = {'start': start_var, 'end': end_var}
        # Constrain start and end times to be within friend's availability
        s.add(start_var >= friends[name]["start_min"])
        s.add(end_var <= friends[name]["end_min"])
        # Meeting duration must be at least the minimum required
        s.add(end_var - start_var >= friends[name]["min_duration"])

    # Define the order of meetings. We'll try to meet all friends and let the solver find a feasible order.
    # For simplicity, we'll attempt to meet all friends and let the solver find a feasible order.
    # However, this is complex, so we'll define a possible order based on time windows.

    # We'll model the sequence as a list where each step is a meeting with a friend.
    # For each step, we'll have constraints based on the previous step's location and time.

    # For this problem, let's assume we can meet all friends, and the solver will find the order.
    # This is a simplification; a more complete approach would involve a TSP-like problem.

    # Alternatively, we can try to meet friends in a specific order and check feasibility.
    # Here's one possible order: Elizabeth, Joseph, Ashley, Kimberly, Helen, Richard, Karen, Robert.

    # Define the order of meetings (this is a heuristic; the solver will adjust times)
    meeting_order = ["Elizabeth", "Joseph", "Ashley", "Kimberly", "Helen", "Richard", "Karen", "Robert"]

    # Add constraints for travel times between meetings
    prev_end = current_time
    prev_location = current_location
    for name in meeting_order:
        if name in friends:
            start_var = meeting_vars[name]['start']
            s.add(start_var >= prev_end + travel_times.get((prev_location, friends[name]["location"]), 0))
            prev_end = meeting_vars[name]['end']
            prev_location = friends[name]["location"]

    # Check if all meetings can be scheduled
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in meeting_order:
            if name in friends:
                start_val = model[meeting_vars[name]['start']].as_long()
                end_val = model[meeting_vars[name]['end']].as_long()
                start_hh = start_val // 60
                start_mm = start_val % 60
                end_hh = end_val // 60
                end_mm = end_val % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_hh:02d}:{start_mm:02d}",
                    "end_time": f"{end_hh:02d}:{end_mm:02d}"
                })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}  # No feasible schedule found

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))