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
            "available_start": 19 * 60,  # 7:00 PM in minutes since 9:00 AM (9:00 AM is 0)
            "available_end": 21 * 60,    # 9:00 PM
            "min_duration": 15,
        },
        {
            "name": "Margaret",
            "location": "Financial District",
            "available_start": 16 * 60 + 30,  # 4:30 PM
            "available_end": 20 * 60 + 15,    # 8:15 PM
            "min_duration": 75,
        },
        {
            "name": "Ronald",
            "location": "North Beach",
            "available_start": 18 * 60 + 30,  # 6:30 PM
            "available_end": 19 * 60 + 30,     # 7:30 PM
            "min_duration": 45,
        },
        {
            "name": "Deborah",
            "location": "The Castro",
            "available_start": 13 * 60 + 45,  # 1:45 PM
            "available_end": 21 * 60 + 15,    # 9:15 PM
            "min_duration": 90,
        },
        {
            "name": "Jeffrey",
            "location": "Golden Gate Park",
            "available_start": 11 * 60 + 15,  # 11:15 AM
            "available_end": 14 * 60 + 30,   # 2:30 PM
            "min_duration": 120,
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

    # Create variables for each meeting's start and end times (in minutes since 9:00 AM)
    meet_vars = {}
    for friend in friends:
        name = friend["name"]
        meet_vars[name] = {
            "start": Int(f"start_{name}"),
            "end": Int(f"end_{name}"),
            "met": Bool(f"met_{name}")  # Whether we met this friend
        }

    # Initial location is Nob Hill at time 0 (9:00 AM)
    initial_location = "Nob Hill"
    current_time = 0

    # Constraints for each meeting
    for friend in friends:
        name = friend["name"]
        start = meet_vars[name]["start"]
        end = meet_vars[name]["end"]
        met = meet_vars[name]["met"]
        available_start = friend["available_start"]
        available_end = friend["available_end"]
        min_duration = friend["min_duration"]

        # If we meet this friend, the meeting must be within their availability
        s.add(Implies(met, start >= available_start))
        s.add(Implies(met, end <= available_end))
        s.add(Implies(met, end >= start + min_duration))
        # If we don't meet them, set start and end to 0
        s.add(Implies(Not(met), start == 0))
        s.add(Implies(Not(met), end == 0))

    # We want to meet as many friends as possible
    num_met = sum([If(meet_vars[name]["met"], 1, 0) for name in meet_vars])
    s.maximize(num_met)

    # Define possible orders (we'll try multiple sequences)
    possible_orders = [
        ["Jeffrey", "Deborah", "Margaret", "Ronald", "Emily"],
        ["Jeffrey", "Deborah", "Ronald", "Margaret", "Emily"],
        ["Deborah", "Jeffrey", "Margaret", "Ronald", "Emily"],
        ["Deborah", "Jeffrey", "Ronald", "Margaret", "Emily"],
    ]

    # Try each possible order until we find a feasible schedule
    for order in possible_orders:
        temp_solver = Solver()
        temp_solver.add(s.assertions())

        # Add constraints for travel times between meetings
        prev_location = initial_location
        prev_end = 0  # starting at 9:00 AM (0 minutes)

        for name in order:
            friend = next(f for f in friends if f["name"] == name)
            current_location = friend["location"]
            travel_time = travel_times[prev_location][current_location]
            start = meet_vars[name]["start"]
            # The current meeting must start after the previous meeting's end + travel time
            temp_solver.add(Implies(meet_vars[name]["met"], start >= prev_end + travel_time))
            # Update previous end time if we met this friend
            prev_end = If(meet_vars[name]["met"], meet_vars[name]["end"], prev_end)
            prev_location = If(meet_vars[name]["met"], current_location, prev_location)

        if temp_solver.check() == sat:
            model = temp_solver.model()
            itinerary = []
            for friend in friends:
                name = friend["name"]
                if model[meet_vars[name]["met"]]:
                    start = model[meet_vars[name]["start"]].as_long()
                    end = model[meet_vars[name]["end"]].as_long()
                    # Convert minutes since 9:00 AM to HH:MM format
                    start_hour = 9 + start // 60
                    start_minute = start % 60
                    end_hour = 9 + end // 60
                    end_minute = end % 60
                    start_time = f"{start_hour:02d}:{start_minute:02d}"
                    end_time = f"{end_hour:02d}:{end_minute:02d}"
                    itinerary.append({
                        "action": "meet",
                        "person": name,
                        "start_time": start_time,
                        "end_time": end_time
                    })
            # Sort itinerary by start time
            itinerary.sort(key=lambda x: x["start_time"])
            return {"itinerary": itinerary}

    return {"error": "No feasible schedule found"}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))