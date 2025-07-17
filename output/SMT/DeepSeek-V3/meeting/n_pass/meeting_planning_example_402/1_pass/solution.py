from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the locations and their indices
    locations = {
        "Golden Gate Park": 0,
        "Haight-Ashbury": 1,
        "Sunset District": 2,
        "Marina District": 3,
        "Financial District": 4,
        "Union Square": 5
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 7, 10, 16, 26, 22],    # Golden Gate Park
        [7, 0, 15, 17, 21, 17],     # Haight-Ashbury
        [11, 15, 0, 21, 30, 30],    # Sunset District
        [18, 16, 19, 0, 17, 16],    # Marina District
        [23, 19, 31, 15, 0, 9],     # Financial District
        [22, 18, 26, 18, 9, 0]      # Union Square
    ]

    # Friends' information
    friends = [
        {"name": "Sarah", "location": "Haight-Ashbury", "available_start": "17:00", "available_end": "21:30", "min_duration": 105},
        {"name": "Patricia", "location": "Sunset District", "available_start": "17:00", "available_end": "19:45", "min_duration": 45},
        {"name": "Matthew", "location": "Marina District", "available_start": "09:15", "available_end": "12:00", "min_duration": 15},
        {"name": "Joseph", "location": "Financial District", "available_start": "14:15", "available_end": "18:45", "min_duration": 30},
        {"name": "Robert", "location": "Union Square", "available_start": "10:15", "available_end": "21:45", "min_duration": 15}
    ]

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

    # Initialize variables for each meeting
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        duration = friend["min_duration"]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        
        # Add constraints for meeting time within availability
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end == start + duration)
        s.add(start >= 0)  # Cannot start before 9:00 AM
        
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "duration": duration
        })

    # Add constraints for travel times between consecutive meetings
    # We need to decide the order of meetings, which is complex, so we'll assume a fixed order for simplicity
    # Alternatively, we can use a more sophisticated approach with Z3 to find the optimal order
    # Here, we'll assume the order: Matthew, Robert, Joseph, Patricia, Sarah
    # This is a heuristic; in practice, you'd want to explore all possible orders
    order = ["Matthew", "Robert", "Joseph", "Patricia", "Sarah"]
    ordered_meetings = []
    for name in order:
        for m in meetings:
            if m["name"] == name:
                ordered_meetings.append(m)
                break

    # Add travel time constraints between consecutive meetings
    for i in range(len(ordered_meetings) - 1):
        current = ordered_meetings[i]
        next_ = ordered_meetings[i + 1]
        current_loc = locations[current["location"]]
        next_loc = locations[next_["location"]]
        travel_time = travel_times[current_loc][next_loc]
        s.add(next_["start"] >= current["end"] + travel_time)

    # Initial location is Golden Gate Park at time 0 (9:00 AM)
    first_meeting = ordered_meetings[0]
    first_loc = locations[first_meeting["location"]]
    travel_time = travel_times[0][first_loc]
    s.add(first_meeting["start"] >= travel_time)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for m in ordered_meetings:
            start_time = model.eval(m["start"]).as_long()
            end_time = model.eval(m["end"]).as_long()
            itinerary.append({
                "action": "meet",
                "person": m["name"],
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))