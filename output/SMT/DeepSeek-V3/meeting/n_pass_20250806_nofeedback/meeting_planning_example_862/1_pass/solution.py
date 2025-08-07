from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Friends and their details
    friends = [
        {"name": "Laura", "location": "Alamo Square", "available_start": "14:30", "available_end": "16:15", "min_duration": 75},
        {"name": "Brian", "location": "Presidio", "available_start": "10:15", "available_end": "17:00", "min_duration": 30},
        {"name": "Karen", "location": "Russian Hill", "available_start": "18:00", "available_end": "20:15", "min_duration": 90},
        {"name": "Stephanie", "location": "North Beach", "available_start": "10:15", "available_end": "16:00", "min_duration": 75},
        {"name": "Helen", "location": "Golden Gate Park", "available_start": "11:30", "available_end": "21:45", "min_duration": 120},
        {"name": "Sandra", "location": "Richmond District", "available_start": "08:00", "available_end": "15:15", "min_duration": 30},
        {"name": "Mary", "location": "Embarcadero", "available_start": "16:45", "available_end": "18:45", "min_duration": 120},
        {"name": "Deborah", "location": "Financial District", "available_start": "19:00", "available_end": "20:45", "min_duration": 105},
        {"name": "Elizabeth", "location": "Marina District", "available_start": "08:30", "available_end": "13:15", "min_duration": 105}
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    # Add available start and end in minutes since 9:00 AM
    for friend in friends:
        friend["available_start_min"] = time_to_minutes(friend["available_start"])
        friend["available_end_min"] = time_to_minutes(friend["available_end"])

    # Create Z3 variables for start and end times of each meeting
    for friend in friends:
        friend["start"] = Int(f'start_{friend["name"]}')
        friend["end"] = Int(f'end_{friend["name"]}')

    # Constraints for each friend
    for friend in friends:
        # Meeting must start within available time
        s.add(friend["start"] >= friend["available_start_min"])
        s.add(friend["end"] <= friend["available_end_min"])
        # Meeting duration must be at least min_duration
        s.add(friend["end"] - friend["start"] >= friend["min_duration"])
        # Start time must be before end time
        s.add(friend["start"] < friend["end"])

    # Travel times dictionary (from_location -> to_location -> minutes)
    travel_times = {
        "Mission District": {
            "Alamo Square": 11,
            "Presidio": 25,
            "Russian Hill": 15,
            "North Beach": 17,
            "Golden Gate Park": 17,
            "Richmond District": 20,
            "Embarcadero": 19,
            "Financial District": 15,
            "Marina District": 19
        },
        "Alamo Square": {
            "Mission District": 10,
            "Presidio": 17,
            "Russian Hill": 13,
            "North Beach": 15,
            "Golden Gate Park": 9,
            "Richmond District": 11,
            "Embarcadero": 16,
            "Financial District": 17,
            "Marina District": 15
        },
        "Presidio": {
            "Mission District": 26,
            "Alamo Square": 19,
            "Russian Hill": 14,
            "North Beach": 18,
            "Golden Gate Park": 12,
            "Richmond District": 7,
            "Embarcadero": 20,
            "Financial District": 23,
            "Marina District": 11
        },
        "Russian Hill": {
            "Mission District": 16,
            "Alamo Square": 15,
            "Presidio": 14,
            "North Beach": 5,
            "Golden Gate Park": 21,
            "Richmond District": 14,
            "Embarcadero": 8,
            "Financial District": 11,
            "Marina District": 7
        },
        "North Beach": {
            "Mission District": 18,
            "Alamo Square": 16,
            "Presidio": 17,
            "Russian Hill": 4,
            "Golden Gate Park": 22,
            "Richmond District": 18,
            "Embarcadero": 6,
            "Financial District": 8,
            "Marina District": 9
        },
        "Golden Gate Park": {
            "Mission District": 17,
            "Alamo Square": 9,
            "Presidio": 11,
            "Russian Hill": 19,
            "North Beach": 23,
            "Richmond District": 7,
            "Embarcadero": 25,
            "Financial District": 26,
            "Marina District": 16
        },
        "Richmond District": {
            "Mission District": 20,
            "Alamo Square": 13,
            "Presidio": 7,
            "Russian Hill": 13,
            "North Beach": 17,
            "Golden Gate Park": 9,
            "Embarcadero": 19,
            "Financial District": 22,
            "Marina District": 9
        },
        "Embarcadero": {
            "Mission District": 20,
            "Alamo Square": 19,
            "Presidio": 20,
            "Russian Hill": 8,
            "North Beach": 5,
            "Golden Gate Park": 25,
            "Richmond District": 21,
            "Financial District": 5,
            "Marina District": 12
        },
        "Financial District": {
            "Mission District": 17,
            "Alamo Square": 17,
            "Presidio": 22,
            "Russian Hill": 11,
            "North Beach": 7,
            "Golden Gate Park": 23,
            "Richmond District": 21,
            "Embarcadero": 4,
            "Marina District": 15
        },
        "Marina District": {
            "Mission District": 20,
            "Alamo Square": 15,
            "Presidio": 10,
            "Russian Hill": 8,
            "North Beach": 11,
            "Golden Gate Park": 18,
            "Richmond District": 11,
            "Embarcadero": 14,
            "Financial District": 17
        }
    }

    # Sequence constraints: order of meetings and travel times
    # We need to define a sequence. For simplicity, we'll try to meet all friends in some order.
    # Create a list of all possible meetings and enforce an order with travel times.
    # This is complex, so we'll use a simplified approach where we pick a subset of friends and order them.

    # For this example, we'll try to meet all friends and find a feasible order.
    # We'll create a list of all permutations and check for feasible schedules.

    # However, Z3 cannot directly handle permutations, so we'll model the order as follows:
    # For each pair of friends (i, j), if i is before j, then end_i + travel_time <= start_j.

    # We'll create a variable for each friend indicating their position in the sequence.
    positions = {friend["name"]: Int(f'pos_{friend["name"]}') for friend in friends}
    # Each position is unique and between 1 and number of friends
    s.add(Distinct([positions[friend["name"]] for friend in friends]))
    for friend in friends:
        s.add(positions[friend["name"]] >= 1)
        s.add(positions[friend["name"]] <= len(friends))

    # For each pair of friends i and j, if i comes before j, then end_i + travel_time <= start_j
    for i in friends:
        for j in friends:
            if i["name"] != j["name"]:
                # i comes before j implies end_i + travel_time(i.location -> j.location) <= start_j
                travel_time = travel_times[i["location"]][j["location"]]
                s.add(Implies(positions[i["name"]] < positions[j["name"]], 
                             i["end"] + travel_time <= j["start"]))

    # Starting point: you start at Mission District at time 0 (9:00 AM)
    # The first meeting must start after travel time from Mission District to the first friend's location.
    for friend in friends:
        travel_time = travel_times["Mission District"][friend["location"]]
        s.add(Implies(positions[friend["name"]] == 1, friend["start"] >= travel_time))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Collect all meetings with their start and end times
        itinerary = []
        for friend in friends:
            start = m.evaluate(friend["start"]).as_long()
            end = m.evaluate(friend["end"]).as_long()
            # Convert minutes back to HH:MM format
            start_hh = (start + 540) // 60
            start_mm = (start + 540) % 60
            end_hh = (end + 540) // 60
            end_mm = (end + 540) % 60
            start_time = f"{start_hh:02d}:{start_mm:02d}"
            end_time = f"{end_hh:02d}:{end_mm:02d}"
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": start_time,
                "end_time": end_time
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))