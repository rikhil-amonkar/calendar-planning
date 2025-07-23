from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define friends and their details
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
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Process friend data
    for friend in friends:
        friend["available_start_min"] = time_to_minutes(friend["available_start"])
        friend["available_end_min"] = time_to_minutes(friend["available_end"])

    # Define travel times (simplified as a dictionary of dictionaries)
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
            "Marina District": 17
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

    # Create variables for each friend's meeting start and end times
    meeting_vars = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        meeting_vars.append((friend, start, end))

    # Constraints for each meeting
    for friend, start, end in meeting_vars:
        s.add(start >= friend["available_start_min"])
        s.add(end <= friend["available_end_min"])
        s.add(end - start >= friend["min_duration"])

    # Starting point: Mission District at 9:00 AM (540 minutes)
    current_location = "Mission District"
    current_time = 540  # 9:00 AM in minutes

    # Prioritize friends based on earliest available start time
    friends_sorted = sorted(friends, key=lambda x: x["available_start_min"])

    # Add travel time constraints for the prioritized order
    prev_time = current_time
    prev_location = current_location
    itinerary = []
    for friend in friends_sorted:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        travel_time = travel_times[prev_location][friend["location"]]
        s.add(start_var >= prev_time + travel_time)
        itinerary.append({
            "name": friend["name"],
            "location": friend["location"],
            "start_var": start_var,
            "end_var": end_var
        })
        prev_time = end_var
        prev_location = friend["location"]

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        result = []
        for entry in itinerary:
            name = entry["name"]
            start = model[entry["start_var"]].as_long()
            end = model[entry["end_var"]].as_long()
            result.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": result}
    else:
        # If no feasible schedule found, try to meet fewer friends
        for i in range(len(friends_sorted)):
            s = Solver()
            # Re-add constraints for each meeting except the i-th friend
            for j, (friend, start, end) in enumerate(meeting_vars):
                if j != i:
                    s.add(start >= friend["available_start_min"])
                    s.add(end <= friend["available_end_min"])
                    s.add(end - start >= friend["min_duration"])
            # Re-add travel time constraints
            prev_time = current_time
            prev_location = current_location
            itinerary = []
            for j, friend in enumerate(friends_sorted):
                if j != i:
                    start_var = Int(f"start_{friend['name']}")
                    end_var = Int(f"end_{friend['name']}")
                    travel_time = travel_times[prev_location][friend["location"]]
                    s.add(start_var >= prev_time + travel_time)
                    itinerary.append({
                        "name": friend["name"],
                        "location": friend["location"],
                        "start_var": start_var,
                        "end_var": end_var
                    })
                    prev_time = end_var
                    prev_location = friend["location"]
            if s.check() == sat:
                model = s.model()
                result = []
                for entry in itinerary:
                    name = entry["name"]
                    start = model[entry["start_var"]].as_long()
                    end = model[entry["end_var"]].as_long()
                    result.append({
                        "action": "meet",
                        "person": name,
                        "start_time": minutes_to_time(start),
                        "end_time": minutes_to_time(end)
                    })
                return {"itinerary": result}
        return {"itinerary": []}

# Run the solver and print the result
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))