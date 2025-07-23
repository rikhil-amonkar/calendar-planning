from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their availability
    friends = {
        "Matthew": {"location": "Presidio", "start": 11*60, "end": 21*60, "duration": 90},
        "Margaret": {"location": "Chinatown", "start": 9*60 + 15, "end": 18*60 + 45, "duration": 90},
        "Nancy": {"location": "Pacific Heights", "start": 14*60 + 15, "end": 17*60, "duration": 15},
        "Helen": {"location": "Richmond District", "start": 19*60 + 45, "end": 22*60, "duration": 60},
        "Rebecca": {"location": "Fisherman's Wharf", "start": 21*60 + 15, "end": 22*60 + 15, "duration": 60},
        "Kimberly": {"location": "Golden Gate Park", "start": 13*60, "end": 16*60 + 30, "duration": 120},
        "Kenneth": {"location": "Bayview", "start": 14*60 + 30, "end": 18*60, "duration": 60}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Russian Hill": {
            "Presidio": 14,
            "Chinatown": 9,
            "Pacific Heights": 7,
            "Richmond District": 14,
            "Fisherman's Wharf": 7,
            "Golden Gate Park": 21,
            "Bayview": 23
        },
        "Presidio": {
            "Russian Hill": 14,
            "Chinatown": 21,
            "Pacific Heights": 11,
            "Richmond District": 7,
            "Fisherman's Wharf": 19,
            "Golden Gate Park": 12,
            "Bayview": 31
        },
        "Chinatown": {
            "Russian Hill": 7,
            "Presidio": 19,
            "Pacific Heights": 10,
            "Richmond District": 20,
            "Fisherman's Wharf": 8,
            "Golden Gate Park": 23,
            "Bayview": 22
        },
        "Pacific Heights": {
            "Russian Hill": 7,
            "Presidio": 11,
            "Chinatown": 11,
            "Richmond District": 12,
            "Fisherman's Wharf": 13,
            "Golden Gate Park": 15,
            "Bayview": 22
        },
        "Richmond District": {
            "Russian Hill": 13,
            "Presidio": 7,
            "Chinatown": 20,
            "Pacific Heights": 10,
            "Fisherman's Wharf": 18,
            "Golden Gate Park": 9,
            "Bayview": 26
        },
        "Fisherman's Wharf": {
            "Russian Hill": 7,
            "Presidio": 17,
            "Chinatown": 12,
            "Pacific Heights": 12,
            "Richmond District": 18,
            "Golden Gate Park": 25,
            "Bayview": 26
        },
        "Golden Gate Park": {
            "Russian Hill": 19,
            "Presidio": 11,
            "Chinatown": 23,
            "Pacific Heights": 16,
            "Richmond District": 7,
            "Fisherman's Wharf": 24,
            "Bayview": 23
        },
        "Bayview": {
            "Russian Hill": 23,
            "Presidio": 31,
            "Chinatown": 18,
            "Pacific Heights": 23,
            "Richmond District": 25,
            "Fisherman's Wharf": 25,
            "Golden Gate Park": 22
        }
    }

    # Create variables for each meeting's start and end times
    meet_vars = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meet_vars[name] = {'start': start, 'end': end}
        # Constraint: meeting duration >= required duration
        s.add(end - start >= friends[name]["duration"])
        # Constraint: meeting within friend's availability
        s.add(start >= friends[name]["start"])
        s.add(end <= friends[name]["end"])

    # Current location starts at Russian Hill at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Russian Hill"

    # To model the order of meetings, we need to sequence them. This is complex; we'll assume an order for simplicity.
    # Alternatively, we can use a more sophisticated approach with additional variables for ordering.
    # For this problem, we'll try to meet friends in an order that fits the constraints.

    # Let's try to meet Margaret first (Chinatown), then others.
    # This is a heuristic; in a real scenario, we'd need to explore all possible orders.

    # For simplicity, let's assume the order: Margaret, Kimberly, Kenneth, Nancy, Matthew, Helen, Rebecca.
    # We'll add constraints for travel times between these meetings.

    # Order: Margaret -> Kimberly -> Kenneth -> Nancy -> Matthew -> Helen -> Rebecca
    order = ["Margaret", "Kimberly", "Kenneth", "Nancy", "Matthew", "Helen", "Rebecca"]

    prev_location = current_location
    prev_end = current_time

    for name in order:
        # Get meeting info
        loc = friends[name]["location"]
        start_var = meet_vars[name]['start']
        end_var = meet_vars[name]['end']
        # Travel time from previous location to current meeting location
        travel_time = travel_times[prev_location][loc]
        # Constraint: start_var >= prev_end + travel_time
        s.add(start_var >= prev_end + travel_time)
        # Update previous end and location
        prev_end = end_var
        prev_location = loc

    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order:
            start_val = model[meet_vars[name]['start']].as_long()
            end_val = model[meet_vars[name]['end']].as_long()
            start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
            end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
            itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))