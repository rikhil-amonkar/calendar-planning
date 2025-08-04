from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver (not optimizer)
    s = Solver()

    # Define friends and their details
    friends = [
        {"name": "Mark", "location": "Marina District", "available_start": "18:45", "available_end": "21:00", "min_duration": 90},
        {"name": "Karen", "location": "Financial District", "available_start": "09:30", "available_end": "12:45", "min_duration": 90},
        {"name": "Barbara", "location": "Alamo Square", "available_start": "10:00", "available_end": "19:30", "min_duration": 90},
        {"name": "Nancy", "location": "Golden Gate Park", "available_start": "16:45", "available_end": "20:00", "min_duration": 105},
        {"name": "David", "location": "The Castro", "available_start": "09:00", "available_end": "18:00", "min_duration": 120},
        {"name": "Linda", "location": "Bayview", "available_start": "18:15", "available_end": "19:45", "min_duration": 45},
        {"name": "Kevin", "location": "Sunset District", "available_start": "10:00", "available_end": "17:45", "min_duration": 120},
        {"name": "Matthew", "location": "Haight-Ashbury", "available_start": "10:15", "available_end": "15:30", "min_duration": 45},
        {"name": "Andrew", "location": "Nob Hill", "available_start": "11:45", "available_end": "16:45", "min_duration": 105}
    ]

    # Simplified travel times (only needed pairs)
    travel_times = {
        ("Russian Hill", "Financial District"): 11,
        ("Financial District", "Alamo Square"): 17,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Sunset District", "Marina District"): 19,
        ("Marina District", "Bayview"): 27,
        ("Bayview", "The Castro"): 19,
        ("The Castro", "Nob Hill"): 16,
        ("Nob Hill", "Russian Hill"): 5
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for friend in friends:
        name = friend["name"]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        # Start and end times as Z3 variables
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")

        # Add constraints for meeting within availability and duration
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end - start >= min_duration)

        meeting_vars[name] = {"start": start, "end": end, "location": friend["location"]}

    # Create a simple sequence of meetings that should work
    # Russian Hill -> Financial District (Karen) -> Alamo Square (Barbara) -> Haight-Ashbury (Matthew)
    # -> Golden Gate Park (Nancy) -> Sunset District (Kevin) -> Marina District (Mark) -> Bayview (Linda)
    # -> The Castro (David) -> Nob Hill (Andrew) -> Russian Hill

    # Define the meeting order
    meeting_order = ["Karen", "Barbara", "Matthew", "Nancy", "Kevin", "Mark", "Linda", "David", "Andrew"]

    # Add constraints for travel times between consecutive meetings
    for i in range(len(meeting_order)-1):
        current = meeting_order[i]
        next_meet = meeting_order[i+1]
        current_loc = meeting_vars[current]["location"]
        next_loc = meeting_vars[next_meet]["location"]
        travel_time = travel_times.get((current_loc, next_loc), 0)
        s.add(meeting_vars[current]["end"] + travel_time <= meeting_vars[next_meet]["start"])

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in meeting_order:
            start_val = m[meeting_vars[name]["start"]].as_long()
            end_val = m[meeting_vars[name]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))