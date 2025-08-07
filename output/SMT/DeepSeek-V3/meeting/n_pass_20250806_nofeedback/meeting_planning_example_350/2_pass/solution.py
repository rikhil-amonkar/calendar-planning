from z3 import *
import json
from itertools import permutations

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = [
        {
            "name": "Mary",
            "location": "Pacific Heights",
            "available_start": "10:00",
            "available_end": "19:00",
            "min_duration": 45,
            "travel_from_prev": {
                "Bayview": 23,
                "Mission District": 15,
                "Haight-Ashbury": 11,
                "Financial District": 13
            }
        },
        {
            "name": "Lisa",
            "location": "Mission District",
            "available_start": "20:30",
            "available_end": "22:00",
            "min_duration": 75,
            "travel_from_prev": {
                "Bayview": 13,
                "Pacific Heights": 16,
                "Haight-Ashbury": 12,
                "Financial District": 17
            }
        },
        {
            "name": "Betty",
            "location": "Haight-Ashbury",
            "available_start": "07:15",
            "available_end": "17:15",
            "min_duration": 90,
            "travel_from_prev": {
                "Bayview": 19,
                "Pacific Heights": 12,
                "Mission District": 11,
                "Financial District": 21
            }
        },
        {
            "name": "Charles",
            "location": "Financial District",
            "available_start": "11:15",
            "available_end": "15:00",
            "min_duration": 120,
            "travel_from_prev": {
                "Bayview": 19,
                "Pacific Heights": 13,
                "Mission District": 17,
                "Haight-Ashbury": 19
            }
        }
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Available time windows in minutes since 9:00 AM (540)
    available_start_times = {
        "Mary": time_to_minutes("10:00") - 540,
        "Lisa": time_to_minutes("20:30") - 540,
        "Betty": time_to_minutes("07:15") - 540,
        "Charles": time_to_minutes("11:15") - 540
    }
    available_end_times = {
        "Mary": time_to_minutes("19:00") - 540,
        "Lisa": time_to_minutes("22:00") - 540,
        "Betty": time_to_minutes("17:15") - 540,
        "Charles": time_to_minutes("15:00") - 540
    }

    # Create Z3 variables for start and end times of each meeting
    start_vars = {}
    end_vars = {}
    for friend in friends:
        name = friend["name"]
        start_vars[name] = Int(f"start_{name}")
        end_vars[name] = Int(f"end_{name}")

    # Constraints for each friend's meeting
    for friend in friends:
        name = friend["name"]
        min_duration = friend["min_duration"]
        s.add(start_vars[name] >= available_start_times[name])
        s.add(end_vars[name] <= available_end_times[name])
        s.add(end_vars[name] == start_vars[name] + min_duration)

    # Constraints for travel times between meetings
    # We need to decide the order of meetings. This is complex, so we'll try all permutations.
    best_schedule = None
    best_num_meetings = 0

    # Try all possible orders of meetings
    for order in permutations(friends):
        temp_s = Solver()
        # Add the same basic constraints
        for friend in friends:
            name = friend["name"]
            min_duration = friend["min_duration"]
            temp_s.add(start_vars[name] >= available_start_times[name])
            temp_s.add(end_vars[name] <= available_end_times[name])
            temp_s.add(end_vars[name] == start_vars[name] + min_duration)

        # Add travel time constraints based on the order
        prev_location = "Bayview"
        prev_end = 0  # starting at 9:00 AM (0 minutes after)
        for i in range(len(order)):
            current_friend = order[i]
            current_name = current_friend["name"]
            travel_time = current_friend["travel_from_prev"][prev_location]
            temp_s.add(start_vars[current_name] >= prev_end + travel_time)
            prev_end = end_vars[current_name]
            prev_location = current_friend["location"]

        # Check if this order is feasible
        if temp_s.check() == sat:
            model = temp_s.model()
            current_num_meetings = len(order)
            if current_num_meetings > best_num_meetings:
                best_num_meetings = current_num_meetings
                # Extract the schedule
                itinerary = []
                for friend in order:
                    name = friend["name"]
                    start = model.evaluate(start_vars[name]).as_long()
                    end = model.evaluate(end_vars[name]).as_long()
                    start_time = minutes_to_time(start + 540)
                    end_time = minutes_to_time(end + 540)
                    itinerary.append({
                        "action": "meet",
                        "person": name,
                        "start_time": start_time,
                        "end_time": end_time
                    })
                best_schedule = itinerary

    if best_schedule is None:
        return {"itinerary": []}
    else:
        return {"itinerary": best_schedule}

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))