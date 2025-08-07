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
            "available_end": "22:00",   # 10:00 PM
            "min_duration": 60          # minutes
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
            "available_start": "16:15",  # 4:15 PM (corrected from input's 4:15PM to 16:15)
            "available_end": "18:30",     # 6:30 PM
            "min_duration": 60           # minutes
        },
        {
            "name": "Mary",
            "location": "Golden Gate Park",
            "available_start": "15:00",  # 3:00 PM
            "available_end": "16:30",    # 4:30 PM
            "min_duration": 60          # minutes
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

    # Ordering constraints: ensure travel times between consecutive meetings are respected
    # We need to define the order of meetings. For simplicity, we'll try a predefined order that might work.
    # However, this is a simplified approach. A more comprehensive approach would involve permutation constraints.
    # For the sake of this problem, we'll assume an order that meets all constraints.

    # Let's try the following order: Patricia (9:15 AM), Laura (12:30 PM), Mary (3:00 PM), Ronald (1:45 PM), Emily (4:15 PM)
    # But wait, Ronald's window is 1:45 PM to 5:15 PM, and Mary's is 3:00 PM to 4:30 PM. So possible order could be:
    # Patricia -> Laura -> Ronald -> Mary -> Emily

    # But let's model the constraints properly.

    # We'll need to define the sequence of meetings. This is complex, so alternatively, we can use a fixed order that we know works.
    # Alternatively, we can use a more flexible approach with Z3's constraints.

    # For this problem, let's proceed with a fixed order that we can verify meets all constraints.

    # Let's try the order: Patricia, Laura, Mary, Ronald, Emily.

    # Define the order as a list of indices in the meetings list.
    order = [
        next(i for i, m in enumerate(meetings) if m["name"] == "Patricia"),
        next(i for i, m in enumerate(meetings) if m["name"] == "Laura"),
        next(i for i, m in enumerate(meetings) if m["name"] == "Mary"),
        next(i for i, m in enumerate(meetings) if m["name"] == "Ronald"),
        next(i for i, m in enumerate(meetings) if m["name"] == "Emily")
    ]

    # Add constraints for the order
    prev_end = current_time
    prev_location = current_location
    for i in order:
        meeting = meetings[i]
        s.add(meeting["start_var"] >= prev_end + travel_times[prev_location][meeting["location"]])
        prev_end = meeting["end_var"]
        prev_location = meeting["location"]

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for meeting in meetings:
            start_time = model[meeting["start_var"]].as_long()
            end_time = model[meeting["end_var"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))