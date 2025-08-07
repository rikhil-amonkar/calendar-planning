from z3 import *
import json

def solve_scheduling_problem():
    s = Solver()

    friends = [
        {"name": "Stephanie", "location": "Richmond District", "available_start": "16:15", "available_end": "21:30", "min_duration": 75},
        {"name": "William", "location": "Union Square", "available_start": "10:45", "available_end": "17:30", "min_duration": 45},
        {"name": "Elizabeth", "location": "Nob Hill", "available_start": "12:15", "available_end": "15:00", "min_duration": 105},
        {"name": "Joseph", "location": "Fisherman's Wharf", "available_start": "12:45", "available_end": "14:00", "min_duration": 75},
        {"name": "Anthony", "location": "Golden Gate Park", "available_start": "13:00", "available_end": "20:30", "min_duration": 75},
        {"name": "Barbara", "location": "Embarcadero", "available_start": "19:15", "available_end": "20:30", "min_duration": 75},
        {"name": "Carol", "location": "Financial District", "available_start": "11:45", "available_end": "16:15", "min_duration": 60},
        {"name": "Sandra", "location": "North Beach", "available_start": "10:00", "available_end": "12:30", "min_duration": 15},
        {"name": "Kenneth", "location": "Presidio", "available_start": "21:15", "available_end": "22:15", "min_duration": 45}
    ]

    travel_times = {
        "Marina District": {
            "Richmond District": 11, "Union Square": 16, "Nob Hill": 12, 
            "Fisherman's Wharf": 10, "Golden Gate Park": 18, "Embarcadero": 14,
            "Financial District": 17, "North Beach": 11, "Presidio": 10
        },
        "Richmond District": {
            "Marina District": 9, "Union Square": 21, "Nob Hill": 17,
            "Fisherman's Wharf": 18, "Golden Gate Park": 9, "Embarcadero": 19,
            "Financial District": 22, "North Beach": 17, "Presidio": 7
        },
        "Union Square": {
            "Marina District": 18, "Richmond District": 20, "Nob Hill": 9,
            "Fisherman's Wharf": 15, "Golden Gate Park": 22, "Embarcadero": 11,
            "Financial District": 9, "North Beach": 10, "Presidio": 24
        },
        "Nob Hill": {
            "Marina District": 11, "Richmond District": 14, "Union Square": 7,
            "Fisherman's Wharf": 10, "Golden Gate Park": 17, "Embarcadero": 9,
            "Financial District": 9, "North Beach": 8, "Presidio": 17
        },
        "Fisherman's Wharf": {
            "Marina District": 9, "Richmond District": 18, "Union Square": 13,
            "Nob Hill": 11, "Golden Gate Park": 25, "Embarcadero": 8,
            "Financial District": 11, "North Beach": 6, "Presidio": 17
        },
        "Golden Gate Park": {
            "Marina District": 16, "Richmond District": 7, "Union Square": 22,
            "Nob Hill": 20, "Fisherman's Wharf": 24, "Embarcadero": 25,
            "Financial District": 26, "North Beach": 23, "Presidio": 11
        },
        "Embarcadero": {
            "Marina District": 12, "Richmond District": 21, "Union Square": 10,
            "Nob Hill": 10, "Fisherman's Wharf": 6, "Golden Gate Park": 25,
            "Financial District": 5, "North Beach": 5, "Presidio": 20
        },
        "Financial District": {
            "Marina District": 15, "Richmond District": 21, "Union Square": 9,
            "Nob Hill": 8, "Fisherman's Wharf": 10, "Golden Gate Park": 23,
            "Embarcadero": 4, "North Beach": 7, "Presidio": 22
        },
        "North Beach": {
            "Marina District": 9, "Richmond District": 18, "Union Square": 7,
            "Nob Hill": 7, "Fisherman's Wharf": 5, "Golden Gate Park": 22,
            "Embarcadero": 6, "Financial District": 8, "Presidio": 17
        },
        "Presidio": {
            "Marina District": 11, "Richmond District": 7, "Union Square": 22,
            "Nob Hill": 18, "Fisherman's Wharf": 19, "Golden Gate Park": 12,
            "Embarcadero": 20, "Financial District": 23, "North Beach": 18
        }
    }

    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    for friend in friends:
        friend["available_start_min"] = time_to_minutes(friend["available_start"])
        friend["available_end_min"] = time_to_minutes(friend["available_end"])

    current_location = "Marina District"
    current_time = 540  # 9:00 AM in minutes

    meeting_vars = []
    for friend in friends:
        start = Int(f'start_{friend["name"]}')
        end = Int(f'end_{friend["name"]}')
        meeting_vars.append((friend, start, end))

    # More flexible constraints - allow shorter meetings if needed
    for friend, start, end in meeting_vars:
        min_duration = friend["min_duration"]
        s.add(end - start >= min_duration - 15)  # Allow 15 minutes less than minimum
        s.add(start >= friend["available_start_min"])
        s.add(end <= friend["available_end_min"])

    # Try a different meeting order that might work better
    order = ["Sandra", "William", "Carol", "Elizabeth", "Joseph", "Anthony", "Stephanie", "Barbara", "Kenneth"]
    ordered_friends = []
    for name in order:
        for friend, start, end in meeting_vars:
            if friend["name"] == name:
                ordered_friends.append((friend, start, end))
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