from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = [
        {
            "name": "Emily",
            "location": "Richmond District",
            "available_start": "19:00",  # 7:00 PM
            "available_end": "21:00",    # 9:00 PM
            "min_duration": 15           # minutes
        },
        {
            "name": "Margaret",
            "location": "Financial District",
            "available_start": "16:30",  # 4:30 PM
            "available_end": "20:15",    # 8:15 PM
            "min_duration": 75          # minutes
        },
        {
            "name": "Ronald",
            "location": "North Beach",
            "available_start": "18:30",  # 6:30 PM
            "available_end": "19:30",    # 7:30 PM
            "min_duration": 45            # minutes
        },
        {
            "name": "Deborah",
            "location": "The Castro",
            "available_start": "13:45",   # 1:45 PM
            "available_end": "21:15",    # 9:15 PM
            "min_duration": 90          # minutes
        },
        {
            "name": "Jeffrey",
            "location": "Golden Gate Park",
            "available_start": "11:15",  # 11:15 AM
            "available_end": "14:30",    # 2:30 PM
            "min_duration": 120         # minutes
        }
    ]

    # Travel times dictionary: from_location -> to_location -> minutes
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

    # Convert HH:MM time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at Nob Hill at 9:00 AM (540 minutes)
    current_location = "Nob Hill"
    current_time = 540  # 9:00 AM in minutes

    # Create variables for each meeting's start and end times
    meeting_vars = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        meeting_vars.append((friend, start, end))

    # Constraints for each meeting
    for friend, start, end in meeting_vars:
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        # Meeting must start and end within the available window
        s.add(start >= available_start)
        s.add(end <= available_end)
        # Meeting duration must be at least min_duration
        s.add(end - start >= min_duration)
        # Start time must be before end time
        s.add(start < end)

    # Sequence constraints: order of meetings and travel times
    # We need to decide the order of meetings. This is a complex part; for simplicity, we'll assume an order and adjust.
    # Alternatively, we can use a more sophisticated approach with additional variables for ordering.
    # For this example, we'll try a specific order and see if it works.

    # Let's try the order: Jeffrey, Deborah, Margaret, Ronald, Emily
    # This is a heuristic; in a real scenario, we might need to try multiple orders or use a more complex model.

    # Assume the order is Jeffrey, Deborah, Margaret, Ronald, Emily
    order = [
        ("Jeffrey", "Golden Gate Park"),
        ("Deborah", "The Castro"),
        ("Margaret", "Financial District"),
        ("Ronald", "North Beach"),
        ("Emily", "Richmond District")
    ]

    # Create variables for the start and end times of each meeting in order
    prev_location = "Nob Hill"
    prev_end = current_time
    constraints = []
    for person, location in order:
        # Find the friend in the list
        friend = next(f for f in friends if f["name"] == person)
        start_var = next(s for (f, s, e) in meeting_vars if f["name"] == person)
        end_var = next(e for (f, s, e) in meeting_vars if f["name"] == person)

        # Travel time from previous location to current
        travel_time = travel_times[prev_location][location]
        s.add(start_var >= prev_end + travel_time)

        # Update previous location and end time
        prev_location = location
        prev_end = end_var

    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend, start, end in meeting_vars:
            start_val = model.evaluate(start).as_long()
            end_val = model.evaluate(end).as_long()
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))