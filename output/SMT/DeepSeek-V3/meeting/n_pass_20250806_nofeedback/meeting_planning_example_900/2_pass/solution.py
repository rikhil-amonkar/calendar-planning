from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 optimizer (instead of Solver)
    opt = Optimize()

    # Define friends and their constraints
    friends = [
        {"name": "Matthew", "location": "The Castro", "start": "16:30", "end": "20:00", "duration": 45},
        {"name": "Rebecca", "location": "Nob Hill", "start": "15:15", "end": "19:15", "duration": 105},
        {"name": "Brian", "location": "Marina District", "start": "14:15", "end": "22:00", "duration": 30},
        {"name": "Emily", "location": "Pacific Heights", "start": "11:15", "end": "19:45", "duration": 15},
        {"name": "Karen", "location": "Haight-Ashbury", "start": "11:45", "end": "17:30", "duration": 30},
        {"name": "Stephanie", "location": "Mission District", "start": "13:00", "end": "15:45", "duration": 75},
        {"name": "James", "location": "Chinatown", "start": "14:30", "end": "19:00", "duration": 120},
        {"name": "Steven", "location": "Russian Hill", "start": "14:00", "end": "20:00", "duration": 30},
        {"name": "Elizabeth", "location": "Alamo Square", "start": "13:00", "end": "17:15", "duration": 120},
        {"name": "William", "location": "Bayview", "start": "18:15", "end": "20:15", "duration": 90}
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # Subtract 540 to make 9:00 AM as 0

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Travel times dictionary (simplified for this example)
    travel_times = {
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Bayview"): 27,
        # Add more as needed; this is a simplified version
    }

    # Create variables for each meeting
    meetings = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        duration = friend["duration"]
        start_window = time_to_minutes(friend["start"])
        end_window = time_to_minutes(friend["end"])
        
        opt.add(start_var >= start_window)
        opt.add(end_var <= end_window)
        opt.add(end_var == start_var + duration)
        opt.add(start_var >= 0)  # Cannot start before 9:00 AM
        
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start_var": start_var,
            "end_var": end_var,
            "duration": duration
        })

    # Add travel time constraints between consecutive meetings
    # Sort meetings by their earliest possible start time (heuristic)
    meetings_sorted = sorted(meetings, key=lambda m: time_to_minutes(friends[[f["name"] for f in friends].index(m["name"])]["start"]))

    # Add constraints for travel times between consecutive meetings
    for i in range(len(meetings_sorted) - 1):
        current = meetings_sorted[i]
        next_ = meetings_sorted[i + 1]
        travel_time = travel_times.get((current["location"], next_["location"]), 0)  # Default to 0 if not found
        opt.add(next_["start_var"] >= current["end_var"] + travel_time)

    # Maximize the total time spent with friends
    total_time = sum([m["end_var"] - m["start_var"] for m in meetings_sorted])
    opt.maximize(total_time)

    # Check if a solution exists
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for meeting in meetings_sorted:
            start = model.eval(meeting["start_var"]).as_long()
            end = model.eval(meeting["end_var"]).as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the optimizer and print the result
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))