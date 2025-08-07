from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = {
        "Karen": {
            "location": "Russian Hill",
            "available_start": "20:45",  # 8:45 PM in 24-hour format
            "available_end": "21:45",    # 9:45 PM in 24-hour format
            "min_duration": 60,         # minutes
        },
        "Jessica": {
            "location": "The Castro",
            "available_start": "15:45",  # 3:45 PM
            "available_end": "19:30",    # 7:30 PM
            "min_duration": 60,
        },
        "Matthew": {
            "location": "Richmond District",
            "available_start": "07:30",  # 7:30 AM
            "available_end": "15:15",    # 3:15 PM
            "min_duration": 15,
        },
        "Michelle": {
            "location": "Marina District",
            "available_start": "10:30",  # 10:30 AM
            "available_end": "18:45",    # 6:45 PM
            "min_duration": 75,
        },
        "Carol": {
            "location": "North Beach",
            "available_start": "12:00",  # 12:00 PM
            "available_end": "17:00",    # 5:00 PM
            "min_duration": 90,
        },
        "Stephanie": {
            "location": "Union Square",
            "available_start": "10:45",  # 10:45 AM
            "available_end": "14:15",    # 2:15 PM
            "min_duration": 30,
        },
        "Linda": {
            "location": "Golden Gate Park",
            "available_start": "10:45",  # 10:45 AM
            "available_end": "22:00",    # 10:00 PM
            "min_duration": 90,
        }
    }

    # Travel times dictionary: from_location -> to_location -> minutes
    travel_times = {
        "Sunset District": {
            "Russian Hill": 24,
            "The Castro": 17,
            "Richmond District": 12,
            "Marina District": 21,
            "North Beach": 29,
            "Union Square": 30,
            "Golden Gate Park": 11
        },
        "Russian Hill": {
            "Sunset District": 23,
            "The Castro": 21,
            "Richmond District": 14,
            "Marina District": 7,
            "North Beach": 5,
            "Union Square": 11,
            "Golden Gate Park": 21
        },
        "The Castro": {
            "Sunset District": 17,
            "Russian Hill": 18,
            "Richmond District": 16,
            "Marina District": 21,
            "North Beach": 20,
            "Union Square": 19,
            "Golden Gate Park": 11
        },
        "Richmond District": {
            "Sunset District": 11,
            "Russian Hill": 13,
            "The Castro": 16,
            "Marina District": 9,
            "North Beach": 17,
            "Union Square": 21,
            "Golden Gate Park": 9
        },
        "Marina District": {
            "Sunset District": 19,
            "Russian Hill": 8,
            "The Castro": 22,
            "Richmond District": 11,
            "North Beach": 11,
            "Union Square": 16,
            "Golden Gate Park": 18
        },
        "North Beach": {
            "Sunset District": 27,
            "Russian Hill": 4,
            "The Castro": 22,
            "Richmond District": 18,
            "Marina District": 9,
            "Union Square": 7,
            "Golden Gate Park": 22
        },
        "Union Square": {
            "Sunset District": 26,
            "Russian Hill": 13,
            "The Castro": 19,
            "Richmond District": 20,
            "Marina District": 18,
            "North Beach": 10,
            "Golden Gate Park": 22
        },
        "Golden Gate Park": {
            "Sunset District": 10,
            "Russian Hill": 19,
            "The Castro": 13,
            "Richmond District": 7,
            "Marina District": 16,
            "North Beach": 24,
            "Union Square": 22
        }
    }

    # Convert HH:MM time to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to HH:MM time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at Sunset District at 9:00 AM (540 minutes)
    current_location = "Sunset District"
    current_time = time_to_minutes("09:00")

    # Create Z3 variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        meeting_vars[name] = (start_var, end_var)

    # Constraints for each friend's meeting
    for name in friends:
        data = friends[name]
        start_var, end_var = meeting_vars[name]
        available_start = time_to_minutes(data["available_start"])
        available_end = time_to_minutes(data["available_end"])
        min_duration = data["min_duration"]

        # Meeting must start and end within the available window
        s.add(start_var >= available_start)
        s.add(end_var <= available_end)
        s.add(end_var >= start_var + min_duration)

    # Ensure meetings are scheduled in a feasible order with travel times
    # We need to sequence the meetings. This is complex, so we'll use a simplified approach:
    # Assume an order and add constraints accordingly. Alternatively, use a more complex model.
    # For simplicity, let's try to meet as many friends as possible in a feasible order.

    # We'll try to meet friends in this order: Matthew, Stephanie, Linda, Michelle, Carol, Jessica, Karen
    # This is a heuristic; in practice, we'd need a more sophisticated approach.
    # For now, let's proceed with this order.

    # Define the order
    order = ["Matthew", "Stephanie", "Linda", "Michelle", "Carol", "Jessica", "Karen"]

    # Add constraints for travel times between meetings
    prev_location = current_location
    prev_end_time = current_time
    for name in order:
        if name not in meeting_vars:
            continue  # skip if not in the list (shouldn't happen here)
        start_var, end_var = meeting_vars[name]
        location = friends[name]["location"]
        travel_time = travel_times[prev_location][location]
        s.add(start_var >= prev_end_time + travel_time)
        prev_location = location
        prev_end_time = end_var

    # Also, ensure that Karen's meeting ends by 21:45 (since she's the last)
    s.add(meeting_vars["Karen"][1] <= time_to_minutes("21:45"))

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order:
            start_var, end_var = meeting_vars[name]
            start_val = model.evaluate(start_var).as_long()
            end_val = model.evaluate(end_var).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}  # No solution found

# Run the solver and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))