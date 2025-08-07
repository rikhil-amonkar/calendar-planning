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

    # Define the order of meetings as a list of indices
    # We'll try to meet Nancy first, then Matthew, then Karen, then Paul, then Carol, then Patricia, then Jeffrey
    meeting_order = [4, 6, 3, 0, 1, 2, 5]  # Indices correspond to the order in the friends list

    # Ensure no overlapping meetings and travel time is accounted for
    prev_end = current_time
    prev_location = current_location
    for i in meeting_order:
        meeting = meetings[i]
        s.add(meeting["start"] >= prev_end + travel_times[prev_location][meeting["location"]])
        prev_end = meeting["end"]
        prev_location = meeting["location"]

    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []

        # Collect all meetings in the order we tried
        for i in meeting_order:
            meeting = meetings[i]
            start_val = model.eval(meeting["start"]).as_long()
            end_val = model.eval(meeting["end"]).as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
result = solve_scheduling()
print(json.dumps(result, indent=2))