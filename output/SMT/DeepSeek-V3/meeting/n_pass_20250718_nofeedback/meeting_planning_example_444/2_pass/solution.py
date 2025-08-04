from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define the friends and their constraints
    friends = {
        "Ronald": {
            "location": "Russian Hill",
            "available_start": (13, 45),  # 1:45 PM
            "available_end": (17, 15),    # 5:15 PM
            "min_duration": 105            # minutes
        },
        "Patricia": {
            "location": "Sunset District",
            "available_start": (9, 15),    # 9:15 AM
            "available_end": (22, 0),      # 10:00 PM
            "min_duration": 60             # minutes
        },
        "Laura": {
            "location": "North Beach",
            "available_start": (12, 30),   # 12:30 PM
            "available_end": (12, 45),     # 12:45 PM
            "min_duration": 15             # minutes
        },
        "Emily": {
            "location": "The Castro",
            "available_start": (16, 15),   # 4:15 PM
            "available_end": (18, 30),     # 6:30 PM
            "min_duration": 60             # minutes
        },
        "Mary": {
            "location": "Golden Gate Park",
            "available_start": (15, 0),    # 3:00 PM
            "available_end": (16, 30),     # 4:30 PM
            "min_duration": 60             # minutes
        }
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Financial District": {
            "Russian Hill": 10,
            "Sunset District": 31,
            "North Beach": 7,
            "The Castro": 23,
            "Golden Gate Park": 23
        },
        "Russian Hill": {
            "Financial District": 11,
            "Sunset District": 23,
            "North Beach": 5,
            "The Castro": 21,
            "Golden Gate Park": 21
        },
        "Sunset District": {
            "Financial District": 30,
            "Russian Hill": 24,
            "North Beach": 29,
            "The Castro": 17,
            "Golden Gate Park": 11
        },
        "North Beach": {
            "Financial District": 8,
            "Russian Hill": 4,
            "Sunset District": 27,
            "The Castro": 22,
            "Golden Gate Park": 22
        },
        "The Castro": {
            "Financial District": 20,
            "Russian Hill": 18,
            "Sunset District": 17,
            "North Beach": 20,
            "Golden Gate Park": 11
        },
        "Golden Gate Park": {
            "Financial District": 26,
            "Russian Hill": 19,
            "Sunset District": 10,
            "North Beach": 24,
            "The Castro": 13
        }
    }

    # Create Z3 variables for each friend's start and end times (in minutes since 9:00 AM)
    start_vars = {}
    end_vars = {}
    for name in friends:
        start_vars[name] = Int(f'start_{name}')
        end_vars[name] = Int(f'end_{name}')

    # Current location starts at Financial District at 9:00 AM (time = 0)
    current_time = 0
    current_location = "Financial District"

    # Define the order of meetings as a permutation of friends
    # We'll use a list to represent the order and let Z3 find the feasible sequence
    order = [Int(f'order_{i}') for i in range(len(friends))]
    # Each order variable should be between 0 and len(friends)-1
    for o in order:
        s.add(o >= 0, o < len(friends))
    # All order variables should be distinct
    s.add(Distinct(order))

    # Constraints for each friend in the order
    prev_end = 0  # starting at 9:00 AM (0 minutes)
    prev_loc = "Financial District"
    for i in range(len(friends)):
        # Get the friend at position i in the order
        name = If(order[i] == 0, "Ronald",
                 If(order[i] == 1, "Patricia",
                  If(order[i] == 2, "Laura",
                   If(order[i] == 3, "Emily",
                    If(order[i] == 4, "Mary", "unknown")))))
        friend = friends[name]
        loc = friend["location"]
        available_start = friend["available_start"][0] * 60 + friend["available_start"][1] - (9 * 60)  # Convert to minutes since 9:00 AM
        available_end = friend["available_end"][0] * 60 + friend["available_end"][1] - (9 * 60)
        min_duration = friend["min_duration"]

        # Travel time from previous location
        travel_time = travel_times[prev_loc][loc]

        # Start time must be >= previous end time + travel time
        s.add(start_vars[name] >= prev_end + travel_time)
        # End time is start time + duration
        s.add(end_vars[name] == start_vars[name] + min_duration)
        # Meeting must be within availability window
        s.add(start_vars[name] >= available_start)
        s.add(end_vars[name] <= available_end)

        # Update previous end and location for next iteration
        prev_end = end_vars[name]
        prev_loc = loc

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract the order of meetings
        order_values = [model.evaluate(o).as_long() for o in order]
        # Map order values to friend names
        friend_names = ["Ronald", "Patricia", "Laura", "Emily", "Mary"]
        ordered_friends = [friend_names[i] for i in order_values]
        itinerary = []
        for name in ordered_friends:
            start = model.evaluate(start_vars[name]).as_long()
            end = model.evaluate(end_vars[name]).as_long()
            # Convert minutes since 9:00 AM to HH:MM
            start_hour = 9 + start // 60
            start_minute = start % 60
            end_hour = 9 + end // 60
            end_minute = end % 60
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_hour:02d}:{start_minute:02d}",
                "end_time": f"{end_hour:02d}:{end_minute:02d}"
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}  # No feasible schedule found

# Solve and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))