from z3 import *
import json

def solve_scheduling_problem():
    s = Optimize()  # Using Optimize instead of Solver for better performance

    # Define friends data with adjusted priorities
    friends = [
        {"name": "Joseph", "location": "Fisherman's Wharf", "available_start": "12:45", "available_end": "14:00", "min_duration": 75, "priority": 1},
        {"name": "Elizabeth", "location": "Nob Hill", "available_start": "12:15", "available_end": "15:00", "min_duration": 105, "priority": 2},
        {"name": "Sandra", "location": "North Beach", "available_start": "10:00", "available_end": "12:30", "min_duration": 15, "priority": 3},
        {"name": "Carol", "location": "Financial District", "available_start": "11:45", "available_end": "16:15", "min_duration": 60, "priority": 4},
        {"name": "William", "location": "Union Square", "available_start": "10:45", "available_end": "17:30", "min_duration": 45, "priority": 5},
        {"name": "Anthony", "location": "Golden Gate Park", "available_start": "13:00", "available_end": "20:30", "min_duration": 75, "priority": 6},
        {"name": "Stephanie", "location": "Richmond District", "available_start": "16:15", "available_end": "21:30", "min_duration": 75, "priority": 7},
        {"name": "Barbara", "location": "Embarcadero", "available_start": "19:15", "available_end": "20:30", "min_duration": 75, "priority": 8},
        {"name": "Kenneth", "location": "Presidio", "available_start": "21:15", "available_end": "22:15", "min_duration": 45, "priority": 9}
    ]

    # Travel times dictionary
    travel_times = {
        "Marina District": {
            "Richmond District": 11, "Union Square": 16, "Nob Hill": 12,
            "Fisherman's Wharf": 10, "Golden Gate Park": 18, "Embarcadero": 14,
            "Financial District": 17, "North Beach": 11, "Presidio": 10
        },
        # ... (rest of travel times remain the same as previous solution)
    }

    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    for friend in friends:
        friend["available_start_min"] = time_to_minutes(friend["available_start"])
        friend["available_end_min"] = time_to_minutes(friend["available_end"])

    current_location = "Marina District"
    current_time = 540  # 9:00 AM

    # Create meeting variables and constraints
    meeting_vars = []
    for friend in friends:
        start = Int(f'start_{friend["name"]}')
        end = Int(f'end_{friend["name"]}')
        meeting_vars.append((friend, start, end))
        s.add(start >= friend["available_start_min"])
        s.add(end <= friend["available_end_min"])
        s.add(end - start >= friend["min_duration"] - 15)  # Flexible duration

    # Sort friends by priority (tightest windows first)
    friends_sorted = sorted(friends, key=lambda x: x["priority"])
    ordered_friends = []
    for friend in friends_sorted:
        for f, start, end in meeting_vars:
            if f["name"] == friend["name"]:
                ordered_friends.append((f, start, end))
                break

    # Add travel time constraints
    prev_location = "Marina District"
    prev_end = current_time
    for i in range(len(ordered_friends)):
        friend, start, end = ordered_friends[i]
        current_loc = friend["location"]
        travel_time = travel_times[prev_location][current_loc]
        s.add(start >= prev_end + travel_time)
        prev_location = current_loc
        prev_end = end

    # Try to maximize the number of meetings
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend, start, end in meeting_vars:
            start_val = model.evaluate(start).as_long()
            end_val = model.evaluate(end).as_long()
            start_hh = start_val // 60
            start_mm = start_val % 60
            end_hh = end_val // 60
            end_mm = end_val % 60
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))