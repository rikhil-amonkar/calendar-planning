from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define the friends and their constraints
    friends = [
        {
            "name": "Ronald",
            "location": "Russian Hill",
            "available_start": "13:45",  # 1:45 PM
            "available_end": "17:15",    # 5:15 PM
            "min_duration": 105          # minutes
        },
        {
            "name": "Patricia",
            "location": "Sunset District",
            "available_start": "09:15",  # 9:15 AM
            "available_end": "22:00",    # 10:00 PM
            "min_duration": 60           # minutes
        },
        {
            "name": "Laura",
            "location": "North Beach",
            "available_start": "12:30",  # 12:30 PM
            "available_end": "12:45",    # 12:45 PM
            "min_duration": 15           # minutes
        },
        {
            "name": "Emily",
            "location": "The Castro",
            "available_start": "16:15",  # 4:15 PM
            "available_end": "18:30",    # 6:30 PM
            "min_duration": 60           # minutes
        },
        {
            "name": "Mary",
            "location": "Golden Gate Park",
            "available_start": "15:00",  # 3:00 PM
            "available_end": "16:30",     # 4:30 PM
            "min_duration": 60            # minutes
        }
    ]

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Financial District": {
            "Russian Hill": 10,
            "Sunset District": 31,
            "North Beach": 7,
            "The Castro": 23,
            "Golden Gate Park": 23
        },
        "Russian Hill": {
            "Financial District": 11,
            "Sunset District": 23,
            "North Beach": 5,
            "The Castro": 21,
            "Golden Gate Park": 21
        },
        "Sunset District": {
            "Financial District": 30,
            "Russian Hill": 24,
            "North Beach": 29,
            "The Castro": 17,
            "Golden Gate Park": 11
        },
        "North Beach": {
            "Financial District": 8,
            "Russian Hill": 4,
            "Sunset District": 27,
            "The Castro": 22,
            "Golden Gate Park": 22
        },
        "The Castro": {
            "Financial District": 20,
            "Russian Hill": 18,
            "Sunset District": 17,
            "North Beach": 20,
            "Golden Gate Park": 11
        },
        "Golden Gate Park": {
            "Financial District": 26,
            "Russian Hill": 19,
            "Sunset District": 10,
            "North Beach": 24,
            "The Castro": 13
        }
    }

    # Convert HH:MM time to minutes since 9:00 AM (540 minutes, since 9:00 AM is 540 minutes past midnight)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hh = (minutes // 60) % 24
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at Financial District at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Financial District"

    # Create variables for each friend's meeting start and end times
    meetings = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start_var": start_var,
            "end_var": end_var,
            "available_start": time_to_minutes(friend["available_start"]),
            "available_end": time_to_minutes(friend["available_end"]),
            "min_duration": friend["min_duration"]
        })

    # Constraints for each meeting
    for meeting in meetings:
        s.add(meeting["start_var"] >= meeting["available_start"])
        s.add(meeting["end_var"] <= meeting["available_end"])
        s.add(meeting["end_var"] == meeting["start_var"] + meeting["min_duration"])

    # Define the order of meetings using auxiliary variables
    # We'll use a list of integers to represent the order
    order = [Int(f"order_{i}") for i in range(len(meetings))]
    # Each order variable must be between 0 and len(meetings) - 1
    for o in order:
        s.add(o >= 0, o < len(meetings))
    # All order variables must be distinct
    s.add(Distinct(order))

    # Constraints to ensure the order is respected with travel times
    # The first meeting must start after traveling from the initial location
    first_meeting = meetings[order[0]]
    s.add(first_meeting["start_var"] >= current_time + travel_times[current_location][first_meeting["location"]])

    # Subsequent meetings must start after the previous meeting ends plus travel time
    for i in range(1, len(meetings)):
        prev_meeting = meetings[order[i - 1]]
        curr_meeting = meetings[order[i]]
        s.add(curr_meeting["start_var"] >= prev_meeting["end_var"] + travel_times[prev_meeting["location"]][curr_meeting["location"]])

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        # Get the order of meetings from the model
        meeting_order = [model[o].as_long() for o in order]
        # Sort meetings according to the order
        sorted_meetings = [meetings[i] for i in meeting_order]
        for meeting in sorted_meetings:
            start_time = model[meeting["start_var"]].as_long()
            end_time = model[meeting["end_var"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))