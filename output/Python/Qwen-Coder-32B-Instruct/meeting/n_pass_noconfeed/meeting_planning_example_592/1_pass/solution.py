import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Nob Hill"): 7,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Nob Hill"): 8,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Nob Hill"): 9,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Nob Hill"): 12,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Golden Gate Park"): 17,
}

# Define meeting constraints
meetings = {
    "James": {"location": "Pacific Heights", "start": "20:00", "end": "22:00", "min_duration": 120},
    "Robert": {"location": "Chinatown", "start": "12:15", "end": "16:45", "min_duration": 90},
    "Jeffrey": {"location": "Union Square", "start": "9:30", "end": "15:30", "min_duration": 120},
    "Carol": {"location": "Mission District", "start": "18:15", "end": "21:15", "min_duration": 15},
    "Mark": {"location": "Golden Gate Park", "start": "11:30", "end": "17:45", "min_duration": 15},
    "Sandra": {"location": "Nob Hill", "start": "8:00", "end": "15:30", "min_duration": 15},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%H:%M")

def find_meeting_times(current_time, meetings):
    available_meetings = []
    for person, details in meetings.items():
        start = parse_time(details["start"])
        end = parse_time(details["end"])
        min_duration = details["min_duration"]
        if current_time <= start:
            meeting_end = start + timedelta(minutes=min_duration)
            if meeting_end <= end:
                available_meetings.append((person, start, meeting_end))
        elif current_time < end:
            meeting_end = current_time + timedelta(minutes=min_duration)
            if meeting_end <= end:
                available_meetings.append((person, current_time, meeting_end))
    return available_meetings

def calculate_schedule(start_time):
    current_time = start_time
    itinerary = []
    visited_locations = set()
    while current_time < parse_time("22:00"):
        available_meetings = find_meeting_times(current_time, meetings)
        if not available_meetings:
            break
        available_meetings.sort(key=lambda x: x[1])
        next_meeting = None
        for person, start, end in available_meetings:
            location = meetings[person]["location"]
            if location not in visited_locations:
                travel_time = travel_times.get((current_location, location), float('inf'))
                if current_time + timedelta(minutes=travel_time) <= start:
                    next_meeting = (person, location, start, end)
                    break
        if next_meeting:
            person, location, start, end = next_meeting
            travel_time = travel_times[(current_location, location)]
            current_time += timedelta(minutes=travel_time)
            itinerary.append({
                "action": "travel",
                "location": location,
                "start_time": format_time(current_time),
                "end_time": format_time(start)
            })
            current_time = start
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(start),
                "end_time": format_time(end)
            })
            current_time = end
            visited_locations.add(location)
        else:
            break
    return itinerary

start_time = parse_time("9:00")
current_location = "North Beach"
itinerary = calculate_schedule(start_time)

output = {"itinerary": itinerary}
print(json.dumps(output))