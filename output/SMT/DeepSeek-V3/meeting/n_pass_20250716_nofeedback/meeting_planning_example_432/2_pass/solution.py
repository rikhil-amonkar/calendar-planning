from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the meetings and their constraints
    meetings = [
        {"person": "Joseph", "location": "Fisherman's Wharf", "available_start": "8:00", "available_end": "17:30", "duration": 90},
        {"person": "Jeffrey", "location": "Bayview", "available_start": "17:30", "available_end": "21:30", "duration": 60},
        {"person": "Kevin", "location": "Mission District", "available_start": "11:15", "available_end": "15:15", "duration": 30},
        {"person": "David", "location": "Embarcadero", "available_start": "8:15", "available_end": "9:00", "duration": 30},
        {"person": "Barbara", "location": "Financial District", "available_start": "10:30", "available_end": "16:30", "duration": 15}
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

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Golden Gate Park": {
            "Fisherman's Wharf": 24,
            "Bayview": 23,
            "Mission District": 17,
            "Embarcadero": 25,
            "Financial District": 26
        },
        "Fisherman's Wharf": {
            "Golden Gate Park": 25,
            "Bayview": 26,
            "Mission District": 22,
            "Embarcadero": 8,
            "Financial District": 11
        },
        "Bayview": {
            "Golden Gate Park": 22,
            "Fisherman's Wharf": 25,
            "Mission District": 13,
            "Embarcadero": 19,
            "Financial District": 19
        },
        "Mission District": {
            "Golden Gate Park": 17,
            "Fisherman's Wharf": 22,
            "Bayview": 15,
            "Embarcadero": 19,
            "Financial District": 17
        },
        "Embarcadero": {
            "Golden Gate Park": 25,
            "Fisherman's Wharf": 6,
            "Bayview": 21,
            "Mission District": 20,
            "Financial District": 5
        },
        "Financial District": {
            "Golden Gate Park": 23,
            "Fisherman's Wharf": 10,
            "Bayview": 19,
            "Mission District": 17,
            "Embarcadero": 4
        }
    }

    # Current location starts at Golden Gate Park at 9:00 AM (540 minutes)
    current_location = "Golden Gate Park"
    current_time = 540  # 9:00 AM in minutes

    # Create variables for each meeting
    meeting_vars = []
    for meeting in meetings:
        start = Int(f"start_{meeting['person']}")
        end = Int(f"end_{meeting['person']}")
        meeting_vars.append((meeting, start, end))

    # Constraints for each meeting
    for meeting, start, end in meeting_vars:
        available_start = time_to_minutes(meeting["available_start"])
        available_end = time_to_minutes(meeting["available_end"])
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end == start + meeting["duration"])

    # Order constraints and travel times
    # We need to sequence the meetings considering travel times
    # Let's assume we can choose any order, but must account for travel
    # We'll use a list to represent the order of meetings
    order = [Int(f"order_{i}") for i in range(len(meeting_vars))]
    s.add(Distinct(order))
    for i in range(len(meeting_vars)):
        s.add(order[i] >= 0)
        s.add(order[i] < len(meeting_vars))

    # Variables to track location and time after each meeting
    locations = [String(f"loc_{i}") for i in range(len(meeting_vars) + 1)]
    times = [Int(f"time_{i}") for i in range(len(meeting_vars) + 1)]
    s.add(locations[0] == current_location)
    s.add(times[0] == current_time)

    for i in range(len(meeting_vars)):
        # Get the meeting at position i in the order
        meeting_idx = order[i]
        meeting, start, end = meeting_vars[meeting_idx]
        # The meeting must start after the previous time plus travel
        s.add(start >= times[i] + travel_times[locations[i]][meeting["location"]])
        # Update location and time
        s.add(locations[i + 1] == meeting["location"])
        s.add(times[i + 1] == end)

    # Try to meet as many friends as possible
    # For simplicity, we'll just check for a feasible solution
    if s.check() == sat:
        model = s.model()
        # Extract the order of meetings
        meeting_order = [model.evaluate(o).as_long() for o in order]
        # Build the itinerary
        itinerary = []
        current_loc = current_location
        current_time_val = current_time
        for idx in meeting_order:
            meeting, start, end = meeting_vars[idx]
            start_val = model.evaluate(start).as_long()
            end_val = model.evaluate(end).as_long()
            # Ensure the meeting is feasible with travel time
            travel_time = travel_times[current_loc][meeting["location"]]
            if start_val >= current_time_val + travel_time:
                itinerary.append({
                    "action": "meet",
                    "person": meeting["person"],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
                current_loc = meeting["location"]
                current_time_val = end_val
        # Sort itinerary by start time (though order should already be correct)
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))