from z3 import *
import json

def solve_scheduling_problem():
    s = Solver()

    # Define friends and their details (times in minutes since midnight)
    friends = [
        {"name": "Karen", "location": "Haight-Ashbury", "start": 1260, "end": 1305, "duration": 45},
        {"name": "Jessica", "location": "Nob Hill", "start": 825, "end": 1260, "duration": 90},
        {"name": "Brian", "location": "Russian Hill", "start": 930, "end": 1305, "duration": 60},
        {"name": "Kenneth", "location": "North Beach", "start": 585, "end": 1260, "duration": 30},
        {"name": "Jason", "location": "Chinatown", "start": 495, "end": 705, "duration": 75},
        {"name": "Stephanie", "location": "Union Square", "start": 885, "end": 1125, "duration": 105},
        {"name": "Kimberly", "location": "Embarcadero", "start": 585, "end": 1170, "duration": 75},
        {"name": "Steven", "location": "Financial District", "start": 435, "end": 1275, "duration": 60},
        {"name": "Mark", "location": "Marina District", "start": 615, "end": 780, "duration": 75}
    ]

    # Travel times dictionary (from, to) -> minutes
    travel_times = {
        ("North Beach", "Chinatown"): 6,
        # Other travel times would be included here
        # ...
    }

    # Create variables for each meeting's start and end times
    meeting_vars = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        meeting_vars.append((friend, start_var, end_var))

    # Add basic meeting constraints
    for friend, start, end in meeting_vars:
        s.add(start >= max(friend["start"], 540))  # 9:00 AM = 540 minutes
        s.add(end <= friend["end"])
        s.add(end == start + friend["duration"])

    # Add no-overlap constraints with travel times
    for i in range(len(meeting_vars)):
        for j in range(len(meeting_vars)):
            if i != j:
                friend_i, start_i, end_i = meeting_vars[i]
                friend_j, start_j, end_j = meeting_vars[j]
                travel_time = travel_times.get((friend_i["location"], friend_j["location"]), 0)
                
                # Either meeting i is before j (with travel time) or vice versa
                s.add(Or(
                    start_j >= end_i + travel_time,
                    start_i >= end_j + travel_times.get((friend_j["location"], friend_i["location"]), 0)
                ))

    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend, start, end in meeting_vars:
            start_val = model[start].as_long()
            end_val = model[end].as_long()
            if start_val >= 540:  # Only include meetings starting at or after 9:00 AM
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": f"{start_val//60:02d}:{start_val%60:02d}",
                    "end_time": f"{end_val//60:02d}:{end_val%60:02d}"
                })
        
        # Sort by start time
        itinerary.sort(key=lambda x: int(x["start_time"][:2])*60 + int(x["start_time"][3:]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))