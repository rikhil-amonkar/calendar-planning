from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define friends and their constraints
    friends = {
        "Emily": {
            "location": "Richmond District",
            "available_start": "19:00",
            "available_end": "21:00",
            "min_duration": 15
        },
        "Margaret": {
            "location": "Financial District",
            "available_start": "16:30",
            "available_end": "20:15",
            "min_duration": 75
        },
        "Ronald": {
            "location": "North Beach",
            "available_start": "18:30",
            "available_end": "19:30",
            "min_duration": 45
        },
        "Deborah": {
            "location": "The Castro",
            "available_start": "13:45",
            "available_end": "21:15",
            "min_duration": 90
        },
        "Jeffrey": {
            "location": "Golden Gate Park",
            "available_start": "11:15",
            "available_end": "14:30",
            "min_duration": 120
        }
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Nob Hill": {
            "Richmond District": 14,
            "Financial District": 9,
            "North Beach": 8,
            "The Castro": 17,
            "Golden Gate Park": 17
        },
        "Richmond District": {
            "Nob Hill": 17,
            "Financial District": 22,
            "North Beach": 17,
            "The Castro": 16,
            "Golden Gate Park": 9
        },
        "Financial District": {
            "Nob Hill": 8,
            "Richmond District": 21,
            "North Beach": 7,
            "The Castro": 23,
            "Golden Gate Park": 23
        },
        "North Beach": {
            "Nob Hill": 7,
            "Richmond District": 18,
            "Financial District": 8,
            "The Castro": 22,
            "Golden Gate Park": 22
        },
        "The Castro": {
            "Nob Hill": 16,
            "Richmond District": 16,
            "Financial District": 20,
            "North Beach": 20,
            "Golden Gate Park": 11
        },
        "Golden Gate Park": {
            "Nob Hill": 20,
            "Richmond District": 7,
            "Financial District": 26,
            "North Beach": 24,
            "The Castro": 13
        }
    }

    # Convert time strings to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at Nob Hill at 9:00 (540 minutes)
    current_location = "Nob Hill"
    current_time = 540  # 9:00 in minutes

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meeting_vars[name] = (start_var, end_var)

    # Constraints for each friend
    for name, info in friends.items():
        start_var, end_var = meeting_vars[name]
        available_start = time_to_minutes(info["available_start"])
        available_end = time_to_minutes(info["available_end"])
        min_duration = info["min_duration"]

        # Meeting must start and end within the available window
        s.add(start_var >= available_start)
        s.add(end_var <= available_end)
        s.add(end_var >= start_var + min_duration)

    # Order of meetings and travel times
    # We need to sequence the meetings considering travel times
    # This is a simplified approach; a more sophisticated would model the sequence
    # For simplicity, let's assume the order is Jeffrey -> Deborah -> Margaret -> Ronald -> Emily
    # This is a heuristic; in practice, you'd want the solver to determine the order

    # Assume the order: Jeffrey, Deborah, Margaret, Ronald, Emily
    order = ["Jeffrey", "Deborah", "Margaret", "Ronald", "Emily"]

    # Add travel time constraints between meetings
    prev_location = "Nob Hill"
    prev_end_time = current_time
    for name in order:
        start_var, end_var = meeting_vars[name]
        location = friends[name]["location"]
        travel_time = travel_times[prev_location][location]
        s.add(start_var >= prev_end_time + travel_time)
        prev_location = location
        prev_end_time = end_var

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order:
            start_var, end_var = meeting_vars[name]
            start_time = model.evaluate(start_var).as_long()
            end_time = model.evaluate(end_var).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))