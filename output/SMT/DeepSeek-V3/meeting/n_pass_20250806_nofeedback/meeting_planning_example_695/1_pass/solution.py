from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = [
        {"name": "Paul", "location": "Nob Hill", "start": "16:15", "end": "21:15", "min_duration": 60},
        {"name": "Carol", "location": "Union Square", "start": "18:00", "end": "20:15", "min_duration": 120},
        {"name": "Patricia", "location": "Chinatown", "start": "20:00", "end": "21:30", "min_duration": 75},
        {"name": "Karen", "location": "The Castro", "start": "17:00", "end": "19:00", "min_duration": 45},
        {"name": "Nancy", "location": "Presidio", "start": "11:45", "end": "22:00", "min_duration": 30},
        {"name": "Jeffrey", "location": "Pacific Heights", "start": "20:00", "end": "20:45", "min_duration": 45},
        {"name": "Matthew", "location": "Russian Hill", "start": "15:45", "end": "21:45", "min_duration": 75}
    ]

    # Travel times dictionary: from_location -> to_location -> minutes
    travel_times = {
        "Bayview": {
            "Nob Hill": 20,
            "Union Square": 17,
            "Chinatown": 18,
            "The Castro": 20,
            "Presidio": 31,
            "Pacific Heights": 23,
            "Russian Hill": 23
        },
        "Nob Hill": {
            "Bayview": 19,
            "Union Square": 7,
            "Chinatown": 6,
            "The Castro": 17,
            "Presidio": 17,
            "Pacific Heights": 8,
            "Russian Hill": 5
        },
        "Union Square": {
            "Bayview": 15,
            "Nob Hill": 9,
            "Chinatown": 7,
            "The Castro": 19,
            "Presidio": 24,
            "Pacific Heights": 15,
            "Russian Hill": 13
        },
        "Chinatown": {
            "Bayview": 22,
            "Nob Hill": 8,
            "Union Square": 7,
            "The Castro": 22,
            "Presidio": 19,
            "Pacific Heights": 10,
            "Russian Hill": 7
        },
        "The Castro": {
            "Bayview": 19,
            "Nob Hill": 16,
            "Union Square": 19,
            "Chinatown": 20,
            "Presidio": 20,
            "Pacific Heights": 16,
            "Russian Hill": 18
        },
        "Presidio": {
            "Bayview": 31,
            "Nob Hill": 18,
            "Union Square": 22,
            "Chinatown": 21,
            "The Castro": 21,
            "Pacific Heights": 11,
            "Russian Hill": 14
        },
        "Pacific Heights": {
            "Bayview": 22,
            "Nob Hill": 8,
            "Union Square": 12,
            "Chinatown": 11,
            "The Castro": 16,
            "Presidio": 11,
            "Russian Hill": 7
        },
        "Russian Hill": {
            "Bayview": 23,
            "Nob Hill": 5,
            "Union Square": 11,
            "Chinatown": 9,
            "The Castro": 21,
            "Presidio": 14,
            "Pacific Heights": 7
        }
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = (minutes // 60) % 24
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at Bayview at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Bayview"

    # Create variables for each meeting: start and end times
    meetings = []
    for friend in friends:
        name = friend["name"]
        location = friend["location"]
        start_window = time_to_minutes(friend["start"])
        end_window = time_to_minutes(friend["end"])
        min_duration = friend["min_duration"]

        start = Int(f"start_{name}")
        end = Int(f"end_{name}")

        # Constraints: meeting must be within the friend's window
        s.add(start >= start_window)
        s.add(end <= end_window)
        s.add(end - start >= min_duration)

        meetings.append({
            "name": name,
            "location": location,
            "start": start,
            "end": end,
            "min_duration": min_duration
        })

    # Ensure no overlapping meetings and travel time is accounted for
    # We'll try to meet as many friends as possible, so we'll prioritize certain meetings
    # Let's try to meet all friends and let Z3 find a feasible schedule
    # Order is important; we'll need to sequence meetings properly

    # To simplify, we'll assume a specific order of meetings and let Z3 find the times
    # Alternatively, we can use a more complex approach with sequencing variables
    # For simplicity, let's assume we meet Nancy first (since she's available all day)
    # Then proceed to others

    # Let's try to meet Nancy first
    nancy_meeting = next(m for m in meetings if m["name"] == "Nancy")
    s.add(nancy_meeting["start"] >= current_time + travel_times[current_location][nancy_meeting["location"]])
    current_time_after_nancy = nancy_meeting["end"]
    current_location_after_nancy = nancy_meeting["location"]

    # Next, let's try to meet Matthew (available from 15:45 to 21:45)
    matthew_meeting = next(m for m in meetings if m["name"] == "Matthew")
    s.add(matthew_meeting["start"] >= current_time_after_nancy + travel_times[current_location_after_nancy][matthew_meeting["location"]])
    current_time_after_matthew = matthew_meeting["end"]
    current_location_after_matthew = matthew_meeting["location"]

    # Next, try to meet Karen (17:00-19:00)
    karen_meeting = next(m for m in meetings if m["name"] == "Karen")
    s.add(karen_meeting["start"] >= current_time_after_matthew + travel_times[current_location_after_matthew][karen_meeting["location"]])
    current_time_after_karen = karen_meeting["end"]
    current_location_after_karen = karen_meeting["location"]

    # Next, try to meet Paul (16:15-21:15)
    paul_meeting = next(m for m in meetings if m["name"] == "Paul")
    s.add(paul_meeting["start"] >= current_time_after_karen + travel_times[current_location_after_karen][paul_meeting["location"]])
    current_time_after_paul = paul_meeting["end"]
    current_location_after_paul = paul_meeting["location"]

    # Next, try to meet Carol (18:00-20:15)
    carol_meeting = next(m for m in meetings if m["name"] == "Carol")
    s.add(carol_meeting["start"] >= current_time_after_paul + travel_times[current_location_after_paul][carol_meeting["location"]])
    current_time_after_carol = carol_meeting["end"]
    current_location_after_carol = carol_meeting["location"]

    # Next, try to meet Patricia (20:00-21:30)
    patricia_meeting = next(m for m in meetings if m["name"] == "Patricia")
    s.add(patricia_meeting["start"] >= current_time_after_carol + travel_times[current_location_after_carol][patricia_meeting["location"]])
    current_time_after_patricia = patricia_meeting["end"]
    current_location_after_patricia = patricia_meeting["location"]

    # Finally, try to meet Jeffrey (20:00-20:45)
    jeffrey_meeting = next(m for m in meetings if m["name"] == "Jeffrey")
    s.add(jeffrey_meeting["start"] >= current_time_after_patricia + travel_times[current_location_after_patricia][jeffrey_meeting["location"]])
    
    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []

        # Collect all meetings in the order we tried
        for meeting in [nancy_meeting, matthew_meeting, karen_meeting, paul_meeting, carol_meeting, patricia_meeting, jeffrey_meeting]:
            start_val = model.eval(meeting["start"]).as_long()
            end_val = model.eval(meeting["end"]).as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })

        # Filter out meetings that couldn't be scheduled (if any)
        valid_itinerary = [m for m in itinerary if m["start_time"] != "00:00"]  # dummy check

        return {"itinerary": valid_itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
result = solve_scheduling()
print(json.dumps(result, indent=2))