from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = [
        {"name": "Amanda", "location": "Marina District", "start": "14:45", "end": "19:30", "duration": 105},
        {"name": "Melissa", "location": "The Castro", "start": "09:30", "end": "17:00", "duration": 30},
        {"name": "Jeffrey", "location": "Fisherman's Wharf", "start": "12:45", "end": "18:45", "duration": 120},
        {"name": "Matthew", "location": "Bayview", "start": "10:15", "end": "13:15", "duration": 30},
        {"name": "Nancy", "location": "Pacific Heights", "start": "17:00", "end": "21:30", "duration": 105},
        {"name": "Karen", "location": "Mission District", "start": "17:30", "end": "20:30", "duration": 105},
        {"name": "Robert", "location": "Alamo Square", "start": "11:15", "end": "17:30", "duration": 120},
        {"name": "Joseph", "location": "Golden Gate Park", "start": "08:30", "end": "21:15", "duration": 105}
    ]

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Travel times dictionary
    travel_times = {
        "Presidio": {
            "Marina District": 11, "The Castro": 21, "Fisherman's Wharf": 19,
            "Bayview": 31, "Pacific Heights": 11, "Mission District": 26,
            "Alamo Square": 19, "Golden Gate Park": 12
        },
        "Marina District": {
            "Presidio": 10, "The Castro": 22, "Fisherman's Wharf": 10,
            "Bayview": 27, "Pacific Heights": 7, "Mission District": 20,
            "Alamo Square": 15, "Golden Gate Park": 18
        },
        "The Castro": {
            "Presidio": 20, "Marina District": 21, "Fisherman's Wharf": 24,
            "Bayview": 19, "Pacific Heights": 16, "Mission District": 7,
            "Alamo Square": 8, "Golden Gate Park": 11
        },
        "Fisherman's Wharf": {
            "Presidio": 17, "Marina District": 9, "The Castro": 27,
            "Bayview": 26, "Pacific Heights": 12, "Mission District": 22,
            "Alamo Square": 21, "Golden Gate Park": 25
        },
        "Bayview": {
            "Presidio": 32, "Marina District": 27, "The Castro": 19,
            "Fisherman's Wharf": 25, "Pacific Heights": 23, "Mission District": 13,
            "Alamo Square": 16, "Golden Gate Park": 22
        },
        "Pacific Heights": {
            "Presidio": 11, "Marina District": 6, "The Castro": 16,
            "Fisherman's Wharf": 13, "Bayview": 22, "Mission District": 15,
            "Alamo Square": 10, "Golden Gate Park": 15
        },
        "Mission District": {
            "Presidio": 25, "Marina District": 19, "The Castro": 7,
            "Fisherman's Wharf": 22, "Bayview": 14, "Pacific Heights": 16,
            "Alamo Square": 11, "Golden Gate Park": 17
        },
        "Alamo Square": {
            "Presidio": 17, "Marina District": 15, "The Castro": 8,
            "Fisherman's Wharf": 19, "Bayview": 16, "Pacific Heights": 10,
            "Mission District": 10, "Golden Gate Park": 9
        },
        "Golden Gate Park": {
            "Presidio": 11, "Marina District": 16, "The Castro": 13,
            "Fisherman's Wharf": 24, "Bayview": 23, "Pacific Heights": 16,
            "Mission District": 17, "Alamo Square": 9
        }
    }

    # Create Z3 variables for each friend's meeting times
    meetings = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start_var": start_var,
            "end_var": end_var,
            "available_start": time_to_minutes(friend["start"]),
            "available_end": time_to_minutes(friend["end"]),
            "duration": friend["duration"]
        })

    # Basic constraints for each meeting
    for meeting in meetings:
        s.add(meeting["start_var"] >= meeting["available_start"])
        s.add(meeting["end_var"] <= meeting["available_end"])
        s.add(meeting["end_var"] - meeting["start_var"] >= meeting["duration"])
        s.add(meeting["end_var"] > meeting["start_var"])

    # Additional constraint: all meetings must start after 9:00 AM (540 minutes)
    arrival_time = time_to_minutes("09:00")
    for meeting in meetings:
        s.add(meeting["start_var"] >= arrival_time)

    # Define a reasonable meeting order that should work
    meeting_order = [
        "Melissa",  # The Castro (9:30-17:00)
        "Matthew",  # Bayview (10:15-13:15)
        "Robert",   # Alamo Square (11:15-17:30)
        "Jeffrey",  # Fisherman's Wharf (12:45-18:45)
        "Amanda",   # Marina District (14:45-19:30)
        "Karen",    # Mission District (17:30-20:30)
        "Nancy",    # Pacific Heights (17:00-21:30)
        "Joseph"    # Golden Gate Park (8:30-21:15)
    ]

    # Add sequencing constraints
    current_location = "Presidio"
    current_time = arrival_time

    for name in meeting_order:
        # Find the meeting with this name
        meeting = None
        for m in meetings:
            if m["name"] == name:
                meeting = m
                break
        
        if meeting:
            # Calculate travel time
            travel_time = travel_times[current_location][meeting["location"]]
            # Meeting must start after current_time + travel_time
            s.add(meeting["start_var"] >= current_time + travel_time)
            # Update current time and location
            current_time = meeting["end_var"]
            current_location = meeting["location"]

    # Check for solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for meeting in meetings:
            start = model.evaluate(meeting["start_var"]).as_long()
            end = model.evaluate(meeting["end_var"]).as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        # Sort by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Solve the problem
result = solve_scheduling()
print(json.dumps(result, indent=2))