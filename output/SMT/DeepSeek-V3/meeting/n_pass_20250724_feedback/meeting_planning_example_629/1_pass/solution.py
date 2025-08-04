from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define locations and travel times
    locations = [
        "Russian Hill", "Presidio", "Chinatown", "Pacific Heights", 
        "Richmond District", "Fisherman's Wharf", "Golden Gate Park", "Bayview"
    ]
    
    # Travel times (in minutes) as a dictionary of dictionaries
    travel_times = {
        "Russian Hill": {
            "Presidio": 14, "Chinatown": 9, "Pacific Heights": 7, 
            "Richmond District": 14, "Fisherman's Wharf": 7, 
            "Golden Gate Park": 21, "Bayview": 23
        },
        "Presidio": {
            "Russian Hill": 14, "Chinatown": 21, "Pacific Heights": 11, 
            "Richmond District": 7, "Fisherman's Wharf": 19, 
            "Golden Gate Park": 12, "Bayview": 31
        },
        "Chinatown": {
            "Russian Hill": 7, "Presidio": 19, "Pacific Heights": 10, 
            "Richmond District": 20, "Fisherman's Wharf": 8, 
            "Golden Gate Park": 23, "Bayview": 22
        },
        "Pacific Heights": {
            "Russian Hill": 7, "Presidio": 11, "Chinatown": 11, 
            "Richmond District": 12, "Fisherman's Wharf": 13, 
            "Golden Gate Park": 15, "Bayview": 22
        },
        "Richmond District": {
            "Russian Hill": 13, "Presidio": 7, "Chinatown": 20, 
            "Pacific Heights": 10, "Fisherman's Wharf": 18, 
            "Golden Gate Park": 9, "Bayview": 26
        },
        "Fisherman's Wharf": {
            "Russian Hill": 7, "Presidio": 17, "Chinatown": 12, 
            "Pacific Heights": 12, "Richmond District": 18, 
            "Golden Gate Park": 25, "Bayview": 26
        },
        "Golden Gate Park": {
            "Russian Hill": 19, "Presidio": 11, "Chinatown": 23, 
            "Pacific Heights": 16, "Richmond District": 7, 
            "Fisherman's Wharf": 24, "Bayview": 23
        },
        "Bayview": {
            "Russian Hill": 23, "Presidio": 31, "Chinatown": 18, 
            "Pacific Heights": 23, "Richmond District": 25, 
            "Fisherman's Wharf": 25, "Golden Gate Park": 22
        }
    }

    # Define friends and their constraints
    friends = [
        {"name": "Matthew", "location": "Presidio", "start": "11:00", "end": "21:00", "duration": 90},
        {"name": "Margaret", "location": "Chinatown", "start": "09:15", "end": "18:45", "duration": 90},
        {"name": "Nancy", "location": "Pacific Heights", "start": "14:15", "end": "17:00", "duration": 15},
        {"name": "Helen", "location": "Richmond District", "start": "19:45", "end": "22:00", "duration": 60},
        {"name": "Rebecca", "location": "Fisherman's Wharf", "start": "21:15", "end": "22:15", "duration": 60},
        {"name": "Kimberly", "location": "Golden Gate Park", "start": "13:00", "end": "16:30", "duration": 120},
        {"name": "Kenneth", "location": "Bayview", "start": "14:30", "end": "18:00", "duration": 60}
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # Subtract 540 to start from 9:00 AM (540 minutes)

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create Z3 variables for each friend's meeting start and end times
    for friend in friends:
        friend["start_var"] = Int(f"start_{friend['name']}")
        friend["end_var"] = Int(f"end_{friend['name']}")
        # Constrain meeting times within friend's availability
        s.add(friend["start_var"] >= time_to_minutes(friend["start"]))
        s.add(friend["end_var"] <= time_to_minutes(friend["end"]))
        # Constrain meeting duration
        s.add(friend["end_var"] - friend["start_var"] >= friend["duration"])

    # Constrain travel times between consecutive meetings
    # We need to define an order of meetings, but since we don't know the order,
    # we'll use a heuristic or try all permutations. For simplicity, we'll assume
    # a fixed order and let Z3 find the optimal times within constraints.
    # Alternatively, we can use a more complex approach with sequencing variables.
    # Here, we'll assume that the order is Margaret -> Kimberly -> Kenneth -> Nancy -> Matthew -> Helen -> Rebecca.
    # This is a heuristic based on time windows and locations.
    order = ["Margaret", "Kimberly", "Kenneth", "Nancy", "Matthew", "Helen", "Rebecca"]
    ordered_friends = [next(f for f in friends if f["name"] == name) for name in order]

    # Starting at Russian Hill at 9:00 AM (0 minutes)
    current_location = "Russian Hill"
    current_time = 0

    for i in range(len(ordered_friends)):
        friend = ordered_friends[i]
        # Travel time from current_location to friend's location
        travel_time = travel_times[current_location][friend["location"]]
        s.add(friend["start_var"] >= current_time + travel_time)
        # Update current_location and current_time
        current_location = friend["location"]
        current_time = friend["end_var"]

    # Ensure no overlapping meetings (since we're meeting one friend at a time)
    for i in range(len(ordered_friends) - 1):
        s.add(ordered_friends[i+1]["start_var"] >= ordered_friends[i]["end_var"] + 
              travel_times[ordered_friends[i]["location"]][ordered_friends[i+1]["location"]])

    # Maximize the number of friends met (all in this case)
    # Since we're meeting all friends, we don't need an optimization objective

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            start = model[friend["start_var"]].as_long()
            end = model[friend["end_var"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the scheduling problem
result = solve_scheduling()
print(json.dumps(result, indent=2))