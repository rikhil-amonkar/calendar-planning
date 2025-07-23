import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input data
locations = ["Nob Hill", "Richmond District", "Financial District", "North Beach", "The Castro", "Golden Gate Park"]
travel_times = {
    "Nob Hill": {"Richmond District": 14, "Financial District": 9, "North Beach": 8, "The Castro": 17, "Golden Gate Park": 17},
    "Richmond District": {"Nob Hill": 17, "Financial District": 22, "North Beach": 17, "The Castro": 16, "Golden Gate Park": 9},
    "Financial District": {"Nob Hill": 8, "Richmond District": 21, "North Beach": 7, "The Castro": 23, "Golden Gate Park": 23},
    "North Beach": {"Nob Hill": 7, "Richmond District": 18, "Financial District": 8, "The Castro": 22, "Golden Gate Park": 22},
    "The Castro": {"Nob Hill": 16, "Richmond District": 16, "Financial District": 20, "North Beach": 20, "Golden Gate Park": 11},
    "Golden Gate Park": {"Nob Hill": 20, "Richmond District": 7, "Financial District": 26, "North Beach": 24, "The Castro": 13}
}

friends = [
    {"name": "Emily", "location": "Richmond District", "start": "19:00", "end": "21:00", "duration": 15},
    {"name": "Margaret", "location": "Financial District", "start": "16:30", "end": "20:15", "duration": 75},
    {"name": "Ronald", "location": "North Beach", "start": "18:30", "end": "19:30", "duration": 45},
    {"name": "Deborah", "location": "The Castro", "start": "13:45", "end": "21:15", "duration": 90},
    {"name": "Jeffrey", "location": "Golden Gate Park", "start": "11:15", "end": "14:30", "duration": 120}
]

current_location = "Nob Hill"
current_time = time_to_minutes("9:00")

def can_meet_friend(current_time, current_location, friend):
    location = friend["location"]
    start = time_to_minutes(friend["start"])
    end = time_to_minutes(friend["end"])
    duration = friend["duration"]
    travel_time = travel_times[current_location][location]
    
    arrival_time = current_time + travel_time
    if arrival_time > end:
        return None
    
    meeting_start = max(arrival_time, start)
    meeting_end = meeting_start + duration
    if meeting_end > end:
        return None
    
    return {
        "start_time": meeting_start,
        "end_time": meeting_end,
        "travel_time": travel_time
    }

def generate_schedules():
    schedules = []
    for perm in permutations(friends):
        schedule = []
        current_loc = "Nob Hill"
        current_time_min = time_to_minutes("9:00")
        valid = True
        for friend in perm:
            meeting = can_meet_friend(current_time_min, current_loc, friend)
            if not meeting:
                valid = False
                break
            schedule.append({
                "friend": friend,
                "start_time": meeting["start_time"],
                "end_time": meeting["end_time"],
                "location": friend["location"]
            })
            current_time_min = meeting["end_time"]
            current_loc = friend["location"]
        if valid:
            schedules.append(schedule)
    return schedules

def find_best_schedule(schedules):
    best_schedule = None
    best_count = 0
    best_total_time = 0
    for schedule in schedules:
        count = len(schedule)
        total_time = schedule[-1]["end_time"] - time_to_minutes("9:00")
        if count > best_count or (count == best_count and total_time < best_total_time):
            best_schedule = schedule
            best_count = count
            best_total_time = total_time
    return best_schedule

schedules = generate_schedules()
best_schedule = find_best_schedule(schedules)

if best_schedule:
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["friend"]["name"],
            "start_time": minutes_to_time(meeting["start_time"]),
            "end_time": minutes_to_time(meeting["end_time"])
        })
    result = {"itinerary": itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))