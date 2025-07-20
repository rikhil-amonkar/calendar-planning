from z3 import *
import itertools

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define the friends and their constraints
    friends = {
        "Ronald": {
            "location": "Nob Hill",
            "available_start": "10:00",
            "available_end": "17:00",
            "min_duration": 105,
        },
        "Sarah": {
            "location": "Russian Hill",
            "available_start": "07:15",
            "available_end": "09:30",
            "min_duration": 45,
        },
        "Helen": {
            "location": "The Castro",
            "available_start": "13:30",
            "available_end": "17:00",
            "min_duration": 120,
        },
        "Joshua": {
            "location": "Sunset District",
            "available_start": "14:15",
            "available_end": "19:30",
            "min_duration": 90,
        },
        "Margaret": {
            "location": "Haight-Ashbury",
            "available_start": "10:15",
            "available_end": "22:00",
            "min_duration": 60,
        }
    }

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location and time
    current_location = "Pacific Heights"
    current_time = time_to_minutes("09:00")

    # Travel times dictionary: from -> to -> minutes
    travel_times = {
        "Pacific Heights": {
            "Nob Hill": 8,
            "Russian Hill": 7,
            "The Castro": 16,
            "Sunset District": 21,
            "Haight-Ashbury": 11,
        },
        "Nob Hill": {
            "Pacific Heights": 8,
            "Russian Hill": 5,
            "The Castro": 17,
            "Sunset District": 25,
            "Haight-Ashbury": 13,
        },
        "Russian Hill": {
            "Pacific Heights": 7,
            "Nob Hill": 5,
            "The Castro": 21,
            "Sunset District": 23,
            "Haight-Ashbury": 17,
        },
        "The Castro": {
            "Pacific Heights": 16,
            "Nob Hill": 16,
            "Russian Hill": 18,
            "Sunset District": 17,
            "Haight-Ashbury": 6,
        },
        "Sunset District": {
            "Pacific Heights": 21,
            "Nob Hill": 27,
            "Russian Hill": 24,
            "The Castro": 17,
            "Haight-Ashbury": 15,
        },
        "Haight-Ashbury": {
            "Pacific Heights": 12,
            "Nob Hill": 15,
            "Russian Hill": 17,
            "The Castro": 6,
            "Sunset District": 15,
        }
    }

    # Since Sarah's availability is before our arrival, we can't meet her.
    # So we exclude Sarah from the friends to meet.
    friends_to_meet = ["Ronald", "Helen", "Joshua", "Margaret"]

    # Generate all possible permutations of the friends to meet
    # We'll try all possible orders to find a feasible schedule
    best_schedule = None
    max_meetings = 0

    for order in itertools.permutations(friends_to_meet):
        # Create variables for each meeting's start and end times
        schedule = {}
        for friend in order:
            schedule[friend] = {
                "start": Int(f"start_{friend}"),
                "end": Int(f"end_{friend}"),
            }

        # Create a solver for this order
        temp_s = Solver()

        # Add constraints for each friend
        prev_location = current_location
        prev_end = current_time
        feasible = True

        for friend in order:
            friend_info = friends[friend]
            loc = friend_info["location"]
            start_var = schedule[friend]["start"]
            end_var = schedule[friend]["end"]
            available_start = time_to_minutes(friend_info["available_start"])
            available_end = time_to_minutes(friend_info["available_end"])
            min_duration = friend_info["min_duration"]

            # Meeting must be within available window
            temp_s.add(start_var >= available_start)
            temp_s.add(end_var <= available_end)
            temp_s.add(end_var == start_var + min_duration)

            # Travel time from previous location
            travel_time = travel_times[prev_location][loc]
            temp_s.add(start_var >= prev_end + travel_time)

            # Update previous location and end time
            prev_location = loc
            prev_end = end_var

        # Check if this order is feasible
        if temp_s.check() == sat:
            model = temp_s.model()
            current_meetings = 0
            itinerary = []
            for friend in order:
                start_val = model.evaluate(schedule[friend]["start"]).as_long()
                end_val = model.evaluate(schedule[friend]["end"]).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": friend,
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val),
                })
                current_meetings += 1

            if current_meetings > max_meetings or (current_meetings == max_meetings and best_schedule is None):
                max_meetings = current_meetings
                best_schedule = itinerary

    if best_schedule is not None:
        return {"itinerary": best_schedule}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(result)