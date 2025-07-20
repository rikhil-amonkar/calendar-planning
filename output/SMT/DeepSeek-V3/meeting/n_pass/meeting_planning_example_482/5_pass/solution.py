from z3 import *
import json
from itertools import permutations

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define friends and their constraints
    friends = [
        {
            "name": "Stephanie",
            "location": "Mission District",
            "available_start": "08:15",
            "available_end": "13:45",
            "min_duration": 90,
        },
        {
            "name": "Sandra",
            "location": "Bayview",
            "available_start": "13:00",
            "available_end": "19:30",
            "min_duration": 15,
        },
        {
            "name": "Richard",
            "location": "Pacific Heights",
            "available_start": "07:15",
            "available_end": "10:15",
            "min_duration": 75,
        },
        {
            "name": "Brian",
            "location": "Russian Hill",
            "available_start": "12:15",
            "available_end": "16:00",
            "min_duration": 120,
        },
        {
            "name": "Jason",
            "location": "Fisherman's Wharf",
            "available_start": "08:30",
            "available_end": "17:45",
            "min_duration": 60,
        }
    ]

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Haight-Ashbury": {
            "Mission District": 11,
            "Bayview": 18,
            "Pacific Heights": 12,
            "Russian Hill": 17,
            "Fisherman's Wharf": 23,
        },
        "Mission District": {
            "Haight-Ashbury": 12,
            "Bayview": 15,
            "Pacific Heights": 16,
            "Russian Hill": 15,
            "Fisherman's Wharf": 22,
        },
        "Bayview": {
            "Haight-Ashbury": 19,
            "Mission District": 13,
            "Pacific Heights": 23,
            "Russian Hill": 23,
            "Fisherman's Wharf": 25,
        },
        "Pacific Heights": {
            "Haight-Ashbury": 11,
            "Mission District": 15,
            "Bayview": 22,
            "Russian Hill": 7,
            "Fisherman's Wharf": 13,
        },
        "Russian Hill": {
            "Haight-Ashbury": 17,
            "Mission District": 16,
            "Bayview": 23,
            "Pacific Heights": 7,
            "Fisherman's Wharf": 7,
        },
        "Fisherman's Wharf": {
            "Haight-Ashbury": 22,
            "Mission District": 22,
            "Bayview": 26,
            "Pacific Heights": 12,
            "Russian Hill": 7,
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

    # Current location starts at Haight-Ashbury at 9:00 AM (540 minutes)
    current_time = time_to_minutes("09:00")
    current_location = "Haight-Ashbury"

    # Generate all possible meeting orders (permutations)
    friend_names = [f["name"] for f in friends]
    for meeting_order in permutations(friend_names):
        s = Solver()
        
        # Create variables for each meeting
        meetings = {}
        for friend in friends:
            name = friend["name"]
            meetings[name] = {
                "start": Int(f"start_{name}"),
                "end": Int(f"end_{name}"),
                "duration": friend["min_duration"],
                "available_start": time_to_minutes(friend["available_start"]),
                "available_end": time_to_minutes(friend["available_end"]),
                "location": friend["location"],
            }
            
            # Add constraints for meeting time within availability
            s.add(meetings[name]["start"] >= meetings[name]["available_start"])
            s.add(meetings[name]["end"] <= meetings[name]["available_end"])
            s.add(meetings[name]["end"] == meetings[name]["start"] + meetings[name]["duration"])

        # Add travel time constraints between meetings in the current order
        prev_end = current_time
        prev_location = current_location
        for name in meeting_order:
            meeting = meetings[name]
            travel_time = travel_times[prev_location][meeting["location"]]
            s.add(meeting["start"] >= prev_end + travel_time)
            prev_end = meeting["end"]
            prev_location = meeting["location"]

        # Check if this order is feasible
        if s.check() == sat:
            model = s.model()
            itinerary = []
            for name in meeting_order:
                meeting = meetings[name]
                start_time = model.eval(meeting["start"]).as_long()
                end_time = model.eval(meeting["end"]).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time),
                })
            return {"itinerary": itinerary}

    # If no permutation worked, return empty itinerary
    return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))