from z3 import *
import json

def solve_scheduling_problem():
    s = Solver()

    # Define friends data
    friends = [
        {"name": "Ronald", "location": "Russian Hill", "available_start": "13:45", "available_end": "17:15", "min_duration": 105},
        {"name": "Patricia", "location": "Sunset District", "available_start": "09:15", "available_end": "22:00", "min_duration": 60},
        {"name": "Laura", "location": "North Beach", "available_start": "12:30", "available_end": "12:45", "min_duration": 15},
        {"name": "Emily", "location": "The Castro", "available_start": "16:15", "available_end": "18:30", "min_duration": 60},
        {"name": "Mary", "location": "Golden Gate Park", "available_start": "15:00", "available_end": "16:30", "min_duration": 60}
    ]

    # Travel times dictionary
    travel_times = {
        "Financial District": {"Russian Hill": 10, "Sunset District": 31, "North Beach": 7, "The Castro": 23, "Golden Gate Park": 23},
        "Sunset District": {"Financial District": 30, "Russian Hill": 24, "North Beach": 29, "The Castro": 17, "Golden Gate Park": 11},
        "North Beach": {"Financial District": 8, "Russian Hill": 4, "Sunset District": 27, "The Castro": 22, "Golden Gate Park": 22},
        "Golden Gate Park": {"Financial District": 26, "Russian Hill": 19, "Sunset District": 10, "North Beach": 24, "The Castro": 13},
        "Russian Hill": {"Financial District": 11, "Sunset District": 23, "North Beach": 5, "The Castro": 21, "Golden Gate Park": 21},
        "The Castro": {"Financial District": 20, "Russian Hill": 18, "Sunset District": 17, "North Beach": 20, "Golden Gate Park": 11}
    }

    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = (minutes // 60) % 24
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    current_time = 540  # 9:00 AM
    current_location = "Financial District"

    # Create meeting variables
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

    # Meeting constraints
    for meeting in meetings:
        s.add(meeting["start_var"] >= meeting["available_start"])
        s.add(meeting["end_var"] <= meeting["available_end"])
        s.add(meeting["end_var"] == meeting["start_var"] + meeting["min_duration"])

    # Define a fixed order that should work
    order = ["Patricia", "Laura", "Mary", "Ronald", "Emily"]
    ordered_meetings = [next(m for m in meetings if m["name"] == name) for name in order]

    # First meeting (Patricia)
    first = ordered_meetings[0]
    s.add(first["start_var"] >= current_time + travel_times[current_location][first["location"]])

    # Subsequent meetings
    for i in range(1, len(ordered_meetings)):
        prev = ordered_meetings[i-1]
        curr = ordered_meetings[i]
        s.add(curr["start_var"] >= prev["end_var"] + travel_times[prev["location"]][curr["location"]])

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for meeting in ordered_meetings:
            start = model[meeting["start_var"]].as_long()
            end = model[meeting["end_var"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))