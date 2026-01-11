import json
from datetime import datetime, timedelta

# Travel times in minutes
travel_times = {
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "North Beach"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "North Beach"): 23,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "North Beach"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "North Beach"): 15,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Nob Hill"): 24,
    ("Sunset District", "North Beach"): 28,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "North Beach"): 8,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Nob Hill"): 7,
}

# Meeting constraints
meetings = [
    {"name": "Kevin", "location": "Pacific Heights", "start": "7:15", "end": "8:45", "duration": 90},
    {"name": "Michelle", "location": "Golden Gate Park", "start": "20:00", "end": "21:00", "duration": 15},
    {"name": "Emily", "location": "Fisherman's Wharf", "start": "16:15", "end": "19:00", "duration": 30},
    {"name": "Mark", "location": "Marina District", "start": "18:15", "end": "19:45", "duration": 75},
    {"name": "Barbara", "location": "Alamo Square", "start": "17:00", "end": "19:00", "duration": 120},
    {"name": "Laura", "location": "Sunset District", "start": "19:00", "end": "21:15", "duration": 75},
    {"name": "Mary", "location": "Nob Hill", "start": "17:30", "end": "19:00", "duration": 45},
    {"name": "Helen", "location": "North Beach", "start": "11:00", "end": "12:15", "duration": 45},
]

# Convert times to minutes since start of day
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def find_schedule():
    start_time = time_to_minutes("9:00")
    current_time = start_time
    location = "Presidio"
    itinerary = []

    # Sort meetings by start time
    meetings.sort(key=lambda x: time_to_minutes(x['start']))

    for meeting in meetings:
        meeting_start = time_to_minutes(meeting['start'])
        meeting_end = time_to_minutes(meeting['end'])
        meeting_duration = meeting['duration']
        
        # Check if we can reach the meeting location in time
        travel_time = travel_times.get((location, meeting['location']), float('inf'))
        if current_time + travel_time + meeting_duration <= meeting_end:
            # We can attend this meeting
            meeting_start_time = max(current_time + travel_time, meeting_start)
            meeting_end_time = meeting_start_time + meeting_duration
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['name'],
                "start_time": f"{meeting_start_time // 60}:{meeting_start_time % 60:02}",
                "end_time": f"{meeting_end_time // 60}:{meeting_end_time % 60:02}"
            })
            current_time = meeting_end_time
            location = meeting['location']

    return itinerary

itinerary = find_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))