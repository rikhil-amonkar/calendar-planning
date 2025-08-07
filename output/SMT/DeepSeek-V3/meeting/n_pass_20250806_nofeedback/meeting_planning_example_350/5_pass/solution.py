from z3 import *
import json
from itertools import permutations

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

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

    # Create Z3 variables
    start_vars = {f["name"]: Int(f"start_{f['name']}") for f in friends}
    end_vars = {f["name"]: Int(f"end_{f['name']}") for f in friends}
    meet_vars = {f["name"]: Bool(f"meet_{f['name']}") for f in friends}

    # Constraints for each friend's meeting
    for friend in friends:
        name = friend["name"]
        s.add(Implies(meet_vars[name], start_vars[name] >= available_start_times[name]))
        s.add(Implies(meet_vars[name], end_vars[name] <= available_end_times[name]))
        s.add(Implies(meet_vars[name], end_vars[name] == start_vars[name] + friend["min_duration"]))
        s.add(Implies(Not(meet_vars[name]), start_vars[name] == 0))
        s.add(Implies(Not(meet_vars[name]), end_vars[name] == 0))

    # We'll try different meeting orders
    possible_sequences = []
    for seq in permutations([f for f in friends if f["name"] != "Lisa"]):
        possible_sequences.append(list(seq) + [next(f for f in friends if f["name"] == "Lisa")])

    best_schedule = None
    best_num_meetings = 0

    for sequence in possible_sequences:
        temp_s = Optimize()
        # Add basic constraints
        for friend in friends:
            name = friend["name"]
            temp_s.add(Implies(meet_vars[name], start_vars[name] >= available_start_times[name]))
            temp_s.add(Implies(meet_vars[name], end_vars[name] <= available_end_times[name]))
            temp_s.add(Implies(meet_vars[name], end_vars[name] == start_vars[name] + friend["min_duration"]))
            temp_s.add(Implies(Not(meet_vars[name]), start_vars[name] == 0))
            temp_s.add(Implies(Not(meet_vars[name]), end_vars[name] == 0))

        # Add travel time constraints
        prev_location = "Bayview"
        prev_end = 0
        for friend in sequence:
            name = friend["name"]
            travel_time = friend["travel_from_prev"][prev_location]
            temp_s.add(Implies(meet_vars[name], start_vars[name] >= prev_end + travel_time))
            prev_end = If(meet_vars[name], end_vars[name], prev_end)
            prev_location = If(meet_vars[name], friend["location"], prev_location)

        # Maximize number of meetings
        temp_s.maximize(Sum([If(meet_vars[f["name"]], 1, 0) for f in friends]))

        if temp_s.check() == sat:
            model = temp_s.model()
            current_num_meetings = sum(1 for f in friends if is_true(model[meet_vars[f["name"]]))
            if current_num_meetings > best_num_meetings:
                best_num_meetings = current_num_meetings
                itinerary = []
                for friend in friends:
                    if is_true(model[meet_vars[friend["name"]]]):
                        start = model.evaluate(start_vars[friend["name"]]).as_long()
                        end = model.evaluate(end_vars[friend["name"]]).as_long()
                        itinerary.append({
                            "action": "meet",
                            "person": friend["name"],
                            "start_time": minutes_to_time(start + 540),
                            "end_time": minutes_to_time(end + 540)
                        })
                best_schedule = itinerary

    if best_schedule is None:
        return {"itinerary": []}
    else:
        # Sort by start time
        best_schedule.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": best_schedule}

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))