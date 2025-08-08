from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define friends and their availability
    friends = {
        "Andrew": {"location": "Golden Gate Park", "start": "11:45", "end": "14:30", "min_duration": 75},
        "Sarah": {"location": "Pacific Heights", "start": "16:15", "end": "18:45", "min_duration": 15},
        "Nancy": {"location": "Presidio", "start": "17:30", "end": "19:15", "min_duration": 60},
        "Rebecca": {"location": "Chinatown", "start": "09:45", "end": "21:30", "min_duration": 90},
        "Robert": {"location": "The Castro", "start": "08:30", "end": "14:15", "min_duration": 30}
    }

    # Define travel times (in minutes) from each location to others
    travel_times = {
        "Union Square": {
            "Golden Gate Park": 22,
            "Pacific Heights": 15,
            "Presidio": 24,
            "Chinatown": 7,
            "The Castro": 19
        },
        "Golden Gate Park": {
            "Union Square": 22,
            "Pacific Heights": 16,
            "Presidio": 11,
            "Chinatown": 23,
            "The Castro": 13
        },
        "Pacific Heights": {
            "Union Square": 12,
            "Golden Gate Park": 15,
            "Presidio": 11,
            "Chinatown": 11,
            "The Castro": 16
        },
        "Presidio": {
            "Union Square": 22,
            "Golden Gate Park": 12,
            "Pacific Heights": 11,
            "Chinatown": 21,
            "The Castro": 21
        },
        "Chinatown": {
            "Union Square": 7,
            "Golden Gate Park": 23,
            "Pacific Heights": 10,
            "Presidio": 19,
            "The Castro": 22
        },
        "The Castro": {
            "Union Square": 19,
            "Golden Gate Park": 11,
            "Pacific Heights": 16,
            "Presidio": 20,
            "Chinatown": 20
        }
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at Union Square at 9:00 AM (540 minutes)
    current_location = "Union Square"
    current_time = 540  # 9:00 AM in minutes

    # Create variables for each meeting
    meetings = {}
    for name in friends:
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        meetings[name] = {
            "start_var": start_var,
            "end_var": end_var,
            "location": friends[name]["location"],
            "min_duration": friends[name]["min_duration"],
            "availability_start": time_to_minutes(friends[name]["start"]),
            "availability_end": time_to_minutes(friends[name]["end"])
        }
        # Constraints: meeting must be within availability window
        s.add(start_var >= meetings[name]["availability_start"])
        s.add(end_var <= meetings[name]["availability_end"])
        s.add(end_var - start_var >= meetings[name]["min_duration"])

    # Define the order of meetings and travel times
    # We need to ensure that travel times are respected between consecutive meetings
    # Since the order is not fixed, we'll need to explore possible sequences
    # For simplicity, we'll assume a fixed order that seems reasonable and adjust constraints accordingly
    # Here, we'll try to meet Rebecca first, then Robert, then Andrew, then Sarah, then Nancy
    # This is a heuristic; in a more complete solution, we'd explore all possible orders

    # Define the order: Rebecca, Robert, Andrew, Sarah, Nancy
    order = ["Rebecca", "Robert", "Andrew", "Sarah", "Nancy"]

    # Add constraints for travel times between meetings
    for i in range(len(order)):
        if i == 0:
            # First meeting: travel from Union Square to Rebecca's location (Chinatown)
            travel_time = travel_times[current_location][meetings[order[i]]["location"]]
            s.add(meetings[order[i]]["start_var"] >= current_time + travel_time)
        else:
            # Subsequent meetings: travel from previous location to current location
            prev_location = meetings[order[i-1]]["location"]
            travel_time = travel_times[prev_location][meetings[order[i]]["location"]]
            s.add(meetings[order[i]]["start_var"] >= meetings[order[i-1]]["end_var"] + travel_time)

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in order:
            start = m[meetings[name]["start_var"]].as_long()
            end = m[meetings[name]["end_var"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))