import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Union Square": {"Mission District": 14, "Fisherman's Wharf": 15, "Russian Hill": 13, "Marina District": 18, "North Beach": 10, "Chinatown": 7, "Pacific Heights": 15, "The Castro": 17, "Nob Hill": 9, "Sunset District": 27},
    "Mission District": {"Union Square": 15, "Fisherman's Wharf": 22, "Russian Hill": 15, "Marina District": 19, "North Beach": 17, "Chinatown": 16, "Pacific Heights": 16, "The Castro": 7, "Nob Hill": 12, "Sunset District": 24},
    "Fisherman's Wharf": {"Union Square": 13, "Mission District": 22, "Russian Hill": 7, "Marina District": 9, "North Beach": 6, "Chinatown": 12, "Pacific Heights": 12, "The Castro": 27, "Nob Hill": 11, "Sunset District": 27},
    "Russian Hill": {"Union Square": 10, "Mission District": 16, "Fisherman's Wharf": 7, "Marina District": 7, "North Beach": 5, "Chinatown": 9, "Pacific Heights": 7, "The Castro": 21, "Nob Hill": 5, "Sunset District": 23},
    "Marina District": {"Union Square": 16, "Mission District": 20, "Fisherman's Wharf": 10, "Russian Hill": 8, "North Beach": 11, "Chinatown": 15, "Pacific Heights": 7, "The Castro": 22, "Nob Hill": 12, "Sunset District": 19},
    "North Beach": {"Union Square": 7, "Mission District": 18, "Fisherman's Wharf": 5, "Russian Hill": 4, "Marina District": 9, "Chinatown": 6, "Pacific Heights": 8, "The Castro": 23, "Nob Hill": 7, "Sunset District": 27},
    "Chinatown": {"Union Square": 7, "Mission District": 17, "Fisherman's Wharf": 8, "Russian Hill": 7, "Marina District": 12, "North Beach": 3, "Pacific Heights": 10, "The Castro": 22, "Nob Hill": 9, "Sunset District": 29},
    "Pacific Heights": {"Union Square": 12, "Mission District": 15, "Fisherman's Wharf": 13, "Russian Hill": 7, "Marina District": 6, "North Beach": 9, "Chinatown": 11, "The Castro": 16, "Nob Hill": 8, "Sunset District": 21},
    "The Castro": {"Union Square": 19, "Mission District": 7, "Fisherman's Wharf": 24, "Russian Hill": 18, "Marina District": 21, "North Beach": 20, "Chinatown": 22, "Pacific Heights": 16, "Nob Hill": 16, "Sunset District": 17},
    "Nob Hill": {"Union Square": 7, "Mission District": 13, "Fisherman's Wharf": 10, "Russian Hill": 5, "Marina District": 11, "North Beach": 8, "Chinatown": 6, "Pacific Heights": 8, "The Castro": 17, "Sunset District": 24},
    "Sunset District": {"Union Square": 30, "Mission District": 25, "Fisherman's Wharf": 29, "Russian Hill": 24, "Marina District": 21, "North Beach": 28, "Chinatown": 30, "Pacific Heights": 21, "The Castro": 17, "Nob Hill": 27}
}

# Define meeting constraints
meetings = {
    "Kevin": {"location": "Mission District", "start": "20:45", "end": "21:45", "duration": 60},
    "Mark": {"location": "Fisherman's Wharf", "start": "17:15", "end": "20:00", "duration": 90},
    "Jessica": {"location": "Russian Hill", "start": "09:00", "end": "15:00", "duration": 120},
    "Jason": {"location": "Marina District", "start": "15:15", "end": "21:45", "duration": 120},
    "John": {"location": "North Beach", "start": "09:45", "end": "18:00", "duration": 15},
    "Karen": {"location": "Chinatown", "start": "16:45", "end": "19:00", "duration": 75},
    "Sarah": {"location": "Pacific Heights", "start": "17:30", "end": "18:15", "duration": 45},
    "Amanda": {"location": "The Castro", "start": "20:00", "end": "21:15", "duration": 60},
    "Nancy": {"location": "Nob Hill", "start": "09:45", "end": "13:00", "duration": 45},
    "Rebecca": {"location": "Sunset District", "start": "08:45", "end": "15:00", "duration": 75}
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m}" if h > 9 else f"{h}:{m:02}"

def can_meet(start, end, duration):
    return time_to_minutes(end) - time_to_minutes(start) >= duration

def find_optimal_schedule():
    current_time = time_to_minutes("09:00")
    current_location = "Union Square"
    itinerary = []

    def add_meeting(person, location, start, end, duration):
        nonlocal current_time, current_location
        travel_time = travel_times[current_location][location]
        if current_time + travel_time + duration <= time_to_minutes(end):
            current_time += travel_time
            itinerary.append({"action": "meet", "location": location, "person": person, "start_time": minutes_to_time(current_time), "end_time": minutes_to_time(current_time + duration)})
            current_time += duration
            current_location = location

    # Prioritize meetings based on availability and duration
    for person, details in sorted(meetings.items(), key=lambda x: (time_to_minutes(x[1]['start']), -x[1]['duration'])):
        if can_meet(details['start'], details['end'], details['duration']):
            add_meeting(person, details['location'], details['start'], details['end'], details['duration'])

    return {"itinerary": itinerary}

schedule = find_optimal_schedule()
print(json.dumps(schedule))