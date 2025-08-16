import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Pacific Heights": {"Marina District": 6, "The Castro": 16, "Richmond District": 12, "Alamo Square": 10, "Financial District": 13, "Presidio": 11, "Mission District": 15, "Nob Hill": 8, "Russian Hill": 7},
    "Marina District": {"Pacific Heights": 7, "The Castro": 22, "Richmond District": 11, "Alamo Square": 15, "Financial District": 17, "Presidio": 10, "Mission District": 20, "Nob Hill": 12, "Russian Hill": 8},
    "The Castro": {"Pacific Heights": 16, "Marina District": 21, "Richmond District": 16, "Alamo Square": 8, "Financial District": 21, "Presidio": 20, "Mission District": 7, "Nob Hill": 16, "Russian Hill": 18},
    "Richmond District": {"Pacific Heights": 10, "Marina District": 9, "The Castro": 16, "Alamo Square": 13, "Financial District": 22, "Presidio": 7, "Mission District": 20, "Nob Hill": 17, "Russian Hill": 13},
    "Alamo Square": {"Pacific Heights": 10, "Marina District": 15, "The Castro": 8, "Richmond District": 11, "Financial District": 17, "Presidio": 17, "Mission District": 10, "Nob Hill": 11, "Russian Hill": 13},
    "Financial District": {"Pacific Heights": 13, "Marina District": 15, "The Castro": 20, "Richmond District": 21, "Alamo Square": 17, "Presidio": 22, "Mission District": 17, "Nob Hill": 9, "Russian Hill": 11},
    "Presidio": {"Pacific Heights": 11, "Marina District": 11, "The Castro": 21, "Richmond District": 7, "Alamo Square": 19, "Financial District": 23, "Mission District": 25, "Nob Hill": 18, "Russian Hill": 14},
    "Mission District": {"Pacific Heights": 16, "Marina District": 19, "The Castro": 7, "Richmond District": 20, "Alamo Square": 11, "Financial District": 15, "Presidio": 25, "Nob Hill": 13, "Russian Hill": 15},
    "Nob Hill": {"Pacific Heights": 8, "Marina District": 11, "The Castro": 17, "Richmond District": 14, "Alamo Square": 11, "Financial District": 9, "Presidio": 17, "Mission District": 13, "Russian Hill": 5},
    "Russian Hill": {"Pacific Heights": 7, "Marina District": 7, "The Castro": 21, "Richmond District": 14, "Alamo Square": 15, "Financial District": 11, "Presidio": 14, "Mission District": 16, "Russian Hill": 5}
}

# Define meeting constraints
meetings = {
    "Linda": {"location": "Marina District", "start": "18:00", "end": "22:00", "min_duration": 30},
    "Kenneth": {"location": "The Castro", "start": "14:45", "end": "16:15", "min_duration": 30},
    "Kimberly": {"location": "Richmond District", "start": "14:15", "end": "22:00", "min_duration": 30},
    "Paul": {"location": "Alamo Square", "start": "21:00", "end": "21:30", "min_duration": 15},
    "Carol": {"location": "Financial District", "start": "10:15", "end": "12:00", "min_duration": 60},
    "Brian": {"location": "Presidio", "start": "10:00", "end": "21:30", "min_duration": 75},
    "Laura": {"location": "Mission District", "start": "16:15", "end": "20:30", "min_duration": 30},
    "Sandra": {"location": "Nob Hill", "start": "9:15", "end": "18:30", "min_duration": 60},
    "Karen": {"location": "Russian Hill", "start": "18:30", "end": "22:00", "min_duration": 75}
}

def time_to_minutes(time_str):
    # Ensure the time string is in HH:MM format
    if len(time_str) == 4:
        time_str = "0" + time_str
    return int(time_str[:2]) * 60 + int(time_str[3:])

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

def can_meet(start, end, min_duration, current_time):
    start_minutes = time_to_minutes(start)
    end_minutes = time_to_minutes(end)
    current_minutes = time_to_minutes(current_time)
    if start_minutes <= current_minutes < end_minutes:
        available_time = end_minutes - current_minutes
        return available_time >= min_duration
    elif current_minutes < start_minutes:
        available_time = end_minutes - start_minutes
        return available_time >= min_duration
    return False

def find_next_meeting(current_location, current_time, remaining_meetings):
    best_meeting = None
    best_time = float('inf')
    for person, details in remaining_meetings.items():
        location = details["location"]
        start = details["start"]
        end = details["end"]
        min_duration = details["min_duration"]
        if can_meet(start, end, min_duration, current_time):
            travel_time = travel_times[current_location][location]
            meet_start_time = max(time_to_minutes(current_time) + travel_time, time_to_minutes(start))
            meet_end_time = min(meet_start_time + min_duration, time_to_minutes(end))
            total_time = meet_end_time - time_to_minutes(current_time)
            if total_time < best_time:
                best_time = total_time
                best_meeting = (person, location, minutes_to_time(meet_start_time), minutes_to_time(meet_end_time))
    return best_meeting

def create_schedule():
    itinerary = []
    current_location = "Pacific Heights"
    current_time = "09:00"  # Ensure the initial time is in HH:MM format
    remaining_meetings = meetings.copy()

    while remaining_meetings:
        next_meeting = find_next_meeting(current_location, current_time, remaining_meetings)
        if not next_meeting:
            break
        person, location, meet_start_time, meet_end_time = next_meeting
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": meet_start_time,
            "end_time": meet_end_time
        })
        current_location = location
        current_time = meet_end_time
        del remaining_meetings[person]

    return {"itinerary": itinerary}

schedule = create_schedule()
print(json.dumps(schedule, indent=2))