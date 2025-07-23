from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    solver = Solver()

    # Define the locations and their travel times
    locations = {
        "Fisherman's Wharf": 0,
        "The Castro": 1,
        "Golden Gate Park": 2,
        "Embarcadero": 3,
        "Russian Hill": 4,
        "Nob Hill": 5,
        "Alamo Square": 6,
        "North Beach": 7
    }

    travel_times = [
        [0, 26, 25, 8, 7, 11, 20, 6],  # Fisherman's Wharf
        [24, 0, 11, 22, 18, 16, 8, 20],  # The Castro
        [24, 13, 0, 25, 19, 20, 10, 24],  # Golden Gate Park
        [6, 25, 25, 0, 8, 10, 19, 5],  # Embarcadero
        [7, 21, 21, 8, 0, 5, 15, 5],  # Russian Hill
        [11, 17, 17, 9, 5, 0, 11, 8],  # Nob Hill
        [19, 8, 9, 17, 13, 11, 0, 15],  # Alamo Square
        [5, 22, 22, 6, 4, 7, 16, 0]   # North Beach
    ]

    # Define the friends and their constraints
    friends = [
        {"name": "Laura", "location": "The Castro", "start": "19:45", "end": "21:30", "min_duration": 105},
        {"name": "Daniel", "location": "Golden Gate Park", "start": "21:15", "end": "21:45", "min_duration": 15},
        {"name": "William", "location": "Embarcadero", "start": "07:00", "end": "09:00", "min_duration": 90},
        {"name": "Karen", "location": "Russian Hill", "start": "14:30", "end": "19:45", "min_duration": 30},
        {"name": "Stephanie", "location": "Nob Hill", "start": "07:30", "end": "09:30", "min_duration": 45},
        {"name": "Joseph", "location": "Alamo Square", "start": "11:30", "end": "12:45", "min_duration": 15},
        {"name": "Kimberly", "location": "North Beach", "start": "15:45", "end": "19:15", "min_duration": 30}
    ]

    # Convert time strings to minutes since 00:00
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each meeting
    meetings = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        duration_var = Int(f"duration_{friend['name']}")
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start_var": start_var,
            "end_var": end_var,
            "duration_var": duration_var,
            "min_duration": friend["min_duration"],
            "window_start": time_to_minutes(friend["start"]),
            "window_end": time_to_minutes(friend["end"])
        })

    # Current location starts at Fisherman's Wharf at 9:00 AM (540 minutes)
    current_location = locations["Fisherman's Wharf"]
    current_time = 540  # 9:00 AM in minutes

    # Add constraints for each meeting
    itinerary = []
    for i, meeting in enumerate(meetings):
        # Meeting must be within the friend's availability window
        solver.add(meeting["start_var"] >= meeting["window_start"])
        solver.add(meeting["end_var"] <= meeting["window_end"])
        # Meeting duration must be at least the minimum required
        solver.add(meeting["end_var"] - meeting["start_var"] >= meeting["min_duration"])
        # Travel time from current location to meeting location
        travel_time = travel_times[current_location][locations[meeting["location"]]]
        solver.add(meeting["start_var"] >= current_time + travel_time)
        # Update current location and time
        current_location = locations[meeting["location"]]
        current_time = meeting["end_var"]

    # Ensure meetings do not overlap
    for i in range(len(meetings)):
        for j in range(i + 1, len(meetings)):
            solver.add(Or(
                meetings[i]["end_var"] <= meetings[j]["start_var"],
                meetings[j]["end_var"] <= meetings[i]["start_var"]
            ))

    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for meeting in meetings:
            start_time = model.eval(meeting["start_var"]).as_long()
            end_time = model.eval(meeting["end_var"]).as_long()
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
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))