from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their availability
    friends = {
        "James": {"location": "Pacific Heights", "start": "20:00", "end": "22:00", "min_duration": 120},
        "Robert": {"location": "Chinatown", "start": "12:15", "end": "16:45", "min_duration": 90},
        "Jeffrey": {"location": "Union Square", "start": "09:30", "end": "15:30", "min_duration": 120},
        "Carol": {"location": "Mission District", "start": "18:15", "end": "21:15", "min_duration": 15},
        "Mark": {"location": "Golden Gate Park", "start": "11:30", "end": "17:45", "min_duration": 15},
        "Sandra": {"location": "Nob Hill", "start": "08:00", "end": "15:30", "min_duration": 15}
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location is North Beach at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "North Beach"

    # Define travel times between locations
    travel_times = {
        "North Beach": {
            "Pacific Heights": 8,
            "Chinatown": 6,
            "Union Square": 7,
            "Mission District": 18,
            "Golden Gate Park": 22,
            "Nob Hill": 7
        },
        "Pacific Heights": {
            "North Beach": 9,
            "Chinatown": 11,
            "Union Square": 12,
            "Mission District": 15,
            "Golden Gate Park": 15,
            "Nob Hill": 8
        },
        "Chinatown": {
            "North Beach": 3,
            "Pacific Heights": 10,
            "Union Square": 7,
            "Mission District": 18,
            "Golden Gate Park": 23,
            "Nob Hill": 8
        },
        "Union Square": {
            "North Beach": 10,
            "Pacific Heights": 15,
            "Chinatown": 7,
            "Mission District": 14,
            "Golden Gate Park": 22,
            "Nob Hill": 9
        },
        "Mission District": {
            "North Beach": 17,
            "Pacific Heights": 16,
            "Chinatown": 16,
            "Union Square": 15,
            "Golden Gate Park": 17,
            "Nob Hill": 12
        },
        "Golden Gate Park": {
            "North Beach": 24,
            "Pacific Heights": 16,
            "Chinatown": 23,
            "Union Square": 22,
            "Mission District": 17,
            "Nob Hill": 20
        },
        "Nob Hill": {
            "North Beach": 8,
            "Pacific Heights": 8,
            "Chinatown": 6,
            "Union Square": 7,
            "Mission District": 13,
            "Golden Gate Park": 17
        }
    }

    # Create Z3 variables for each meeting's start and end times
    meetings = {}
    for name in friends:
        meetings[name] = {
            "start": Int(f"start_{name}"),
            "end": Int(f"end_{name}"),
            "location": friends[name]["location"],
            "min_start": time_to_minutes(friends[name]["start"]),
            "max_end": time_to_minutes(friends[name]["end"]),
            "min_duration": friends[name]["min_duration"]
        }
        # Constrain meetings to be within their availability
        s.add(meetings[name]["start"] >= meetings[name]["min_start"])
        s.add(meetings[name]["end"] <= meetings[name]["max_end"])
        s.add(meetings[name]["end"] - meetings[name]["start"] >= meetings[name]["min_duration"])

    # Define the order of meetings and travel times
    # We need to sequence the meetings considering travel times
    # This is a complex constraint; we'll try to find a feasible order

    # Let's assume an order and add constraints accordingly
    # For simplicity, we'll try to meet Jeffrey first (since he's available earliest)
    # Then proceed to others

    # Define a possible order: Jeffrey, Sandra, Robert, Mark, Carol, James
    # This is one possible order; the solver will adjust if it's not feasible
    order = ["Jeffrey", "Sandra", "Robert", "Mark", "Carol", "James"]

    # Add constraints for travel times between meetings
    prev_location = current_location
    prev_end = current_time
    for name in order:
        meeting = meetings[name]
        # Travel time from previous location to current meeting location
        travel_time = travel_times[prev_location][meeting["location"]]
        # Meeting must start after previous end plus travel time
        s.add(meeting["start"] >= prev_end + travel_time)
        prev_end = meeting["end"]
        prev_location = meeting["location"]

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order:
            start = model[meetings[name]["start"]].as_long()
            end = model[meetings[name]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))