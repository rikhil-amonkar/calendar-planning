from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the friends and their details
    friends = [
        {"name": "Rebecca", "location": "Presidio", "start": "18:15", "end": "20:45", "duration": 60},
        {"name": "Linda", "location": "Sunset District", "start": "15:30", "end": "19:45", "duration": 30},
        {"name": "Elizabeth", "location": "Haight-Ashbury", "start": "17:15", "end": "19:30", "duration": 105},
        {"name": "William", "location": "Mission District", "start": "13:15", "end": "19:30", "duration": 30},
        {"name": "Robert", "location": "Golden Gate Park", "start": "14:15", "end": "21:30", "duration": 45},
        {"name": "Mark", "location": "Russian Hill", "start": "10:00", "end": "21:15", "duration": 75}
    ]

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "The Castro": {
            "Presidio": 20,
            "Sunset District": 17,
            "Haight-Ashbury": 6,
            "Mission District": 7,
            "Golden Gate Park": 11,
            "Russian Hill": 18
        },
        "Presidio": {
            "The Castro": 21,
            "Sunset District": 15,
            "Haight-Ashbury": 15,
            "Mission District": 26,
            "Golden Gate Park": 12,
            "Russian Hill": 14
        },
        "Sunset District": {
            "The Castro": 17,
            "Presidio": 16,
            "Haight-Ashbury": 15,
            "Mission District": 24,
            "Golden Gate Park": 11,
            "Russian Hill": 24
        },
        "Haight-Ashbury": {
            "The Castro": 6,
            "Presidio": 15,
            "Sunset District": 15,
            "Mission District": 11,
            "Golden Gate Park": 7,
            "Russian Hill": 17
        },
        "Mission District": {
            "The Castro": 7,
            "Presidio": 25,
            "Sunset District": 24,
            "Haight-Ashbury": 12,
            "Golden Gate Park": 17,
            "Russian Hill": 15
        },
        "Golden Gate Park": {
            "The Castro": 13,
            "Presidio": 11,
            "Sunset District": 10,
            "Haight-Ashbury": 7,
            "Mission District": 17,
            "Russian Hill": 19
        },
        "Russian Hill": {
            "The Castro": 21,
            "Presidio": 14,
            "Sunset District": 23,
            "Haight-Ashbury": 17,
            "Mission District": 16,
            "Golden Gate Park": 21
        }
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each friend's meeting start and end times
    meeting_starts = {}
    meeting_ends = {}
    for friend in friends:
        name = friend["name"]
        meeting_starts[name] = Int(f"start_{name}")
        meeting_ends[name] = Int(f"end_{name}")

    # Add constraints for each friend's availability and duration
    for friend in friends:
        name = friend["name"]
        start_avail = time_to_minutes(friend["start"])
        end_avail = time_to_minutes(friend["end"])
        duration = friend["duration"]

        s.add(meeting_starts[name] >= start_avail)
        s.add(meeting_ends[name] <= end_avail)
        s.add(meeting_ends[name] == meeting_starts[name] + duration)

    # Add constraints for travel times between meetings
    # We need to ensure that the time between the end of one meeting and the start of the next
    # is at least the travel time between their locations.
    # We'll assume the order of meetings is arbitrary and let Z3 figure it out.
    # To simplify, we'll assume we can meet all friends, and let Z3 find a feasible schedule.

    # We'll create a list of all possible meeting orders and add constraints accordingly.
    # However, this is computationally expensive, so we'll instead assume a fixed order
    # based on the earliest possible start times.

    # Alternatively, we can model the problem as a sequence of meetings with travel times.
    # For simplicity, we'll assume we can meet all friends and let Z3 find a feasible schedule.

    # To model the sequence, we can use a list of meetings and ensure that the start time
    # of each meeting is after the end time of the previous meeting plus travel time.

    # We'll create a list of all meetings and add constraints for the order.
    # For simplicity, we'll assume we can meet all friends and let Z3 find a feasible schedule.

    # Since the problem is complex, we'll instead use a heuristic to order the meetings
    # and then verify the constraints.

    # For the sake of this example, we'll assume the following order:
    # Mark, William, Robert, Linda, Elizabeth, Rebecca
    # This is based on their earliest availability and durations.

    # Define the order of meetings
    meeting_order = ["Mark", "William", "Robert", "Linda", "Elizabeth", "Rebecca"]

    # Add constraints for travel times between meetings
    for i in range(len(meeting_order) - 1):
        current = next(f for f in friends if f["name"] == meeting_order[i])
        next_friend = next(f for f in friends if f["name"] == meeting_order[i + 1])
        travel_time = travel_times[current["location"]][next_friend["location"]]
        s.add(meeting_starts[next_friend["name"]] >= meeting_ends[current["name"]] + travel_time)

    # Add constraint for the first meeting (starting at The Castro at 9:00 AM)
    first_meeting = next(f for f in friends if f["name"] == meeting_order[0])
    travel_time_first = travel_times["The Castro"][first_meeting["location"]]
    s.add(meeting_starts[first_meeting["name"]] >= travel_time_first)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            name = friend["name"]
            start = model[meeting_starts[name]].as_long()
            end = model[meeting_ends[name]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))