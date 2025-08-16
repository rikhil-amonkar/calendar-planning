import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Pacific Heights": {"Marina District": 6, "The Castro": 16, "Richmond District": 12, "Alamo Square": 10, "Financial District": 13, "Presidio": 11, "Mission District": 15, "Nob Hill": 8, "Russian Hill": 7},
    "Marina District": {"Pacific Heights": 7, "The Castro": 22, "Richmond District": 11, "Alamo Square": 15, "Financial District": 17, "Presidio": 10, "Mission District": 20, "Nob Hill": 12, "Russian Hill": 8},
    "The Castro": {"Pacific Heights": 16, "Marina District": 21, "Richmond District": 16, "Alamo Square": 8, "Financial District": 21, "Presidio": 20, "Mission District": 7, "Nob Hill": 16, "Russian Hill": 18},
    "Richmond District": {"Pacific Heights": 12, "Marina District": 11, "The Castro": 16, "Alamo Square": 13, "Financial District": 22, "Presidio": 7, "Mission District": 20, "Nob Hill": 17, "Russian Hill": 13},
    "Alamo Square": {"Pacific Heights": 10, "Marina District": 15, "The Castro": 8, "Richmond District": 11, "Financial District": 17, "Presidio": 17, "Mission District": 10, "Nob Hill": 11, "Russian Hill": 13},
    "Financial District": {"Pacific Heights": 13, "Marina District": 15, "The Castro": 20, "Richmond District": 21, "Alamo Square": 17, "Presidio": 22, "Mission District": 17, "Nob Hill": 8, "Russian Hill": 11},
    "Presidio": {"Pacific Heights": 11, "Marina District": 11, "The Castro": 21, "Richmond District": 7, "Alamo Square": 19, "Financial District": 23, "Mission District": 25, "Nob Hill": 18, "Russian Hill": 14},
    "Mission District": {"Pacific Heights": 15, "Marina District": 19, "The Castro": 7, "Richmond District": 20, "Alamo Square": 10, "Financial District": 17, "Presidio": 25, "Nob Hill": 13, "Russian Hill": 15},
    "Nob Hill": {"Pacific Heights": 8, "Marina District": 11, "The Castro": 17, "Richmond District": 14, "Alamo Square": 11, "Financial District": 8, "Presidio": 17, "Mission District": 13, "Russian Hill": 5},
    "Russian Hill": {"Pacific Heights": 7, "Marina District": 8, "The Castro": 21, "Richmond District": 14, "Alamo Square": 15, "Financial District": 11, "Presidio": 14, "Mission District": 16, "Russian Hill": 5}
}

# Define meeting constraints
meetings = {
    "Linda": {"location": "Marina District", "start": "18:00", "end": "22:00", "duration": 30},
    "Kenneth": {"location": "The Castro", "start": "14:45", "end": "16:15", "duration": 30},
    "Kimberly": {"location": "Richmond District", "start": "14:15", "end": "22:00", "duration": 30},
    "Paul": {"location": "Alamo Square", "start": "21:00", "end": "21:30", "duration": 15},
    "Carol": {"location": "Financial District", "start": "10:15", "end": "12:00", "duration": 60},
    "Brian": {"location": "Presidio", "start": "10:00", "end": "21:30", "duration": 75},
    "Laura": {"location": "Mission District", "start": "16:15", "end": "20:30", "duration": 30},
    "Sandra": {"location": "Nob Hill", "start": "09:15", "end": "18:30", "duration": 60},
    "Karen": {"location": "Russian Hill", "start": "18:30", "end": "22:00", "duration": 75}
}

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes}" if minutes >= 10 else f"{hours}:0{minutes}"

def find_meeting_schedule():
    start_time = time_to_minutes("09:00")
    current_location = "Pacific Heights"
    itinerary = []

    def can_meet(meeting, start_time):
        meeting_start = time_to_minutes(meeting["start"])
        meeting_end = time_to_minutes(meeting["end"])
        return meeting_start <= start_time < meeting_end - meeting["duration"]

    def find_next_meeting(start_time, current_location):
        for person, meeting in meetings.items():
            if can_meet(meeting, start_time):
                travel_time = travel_times[current_location][meeting["location"]]
                meeting_start = start_time + travel_time
                if can_meet(meeting, meeting_start):
                    return person, meeting, meeting_start
        return None, None, None

    while True:
        next_person, next_meeting, next_start = find_next_meeting(start_time, current_location)
        if not next_person:
            break

        travel_time = travel_times[current_location][next_meeting["location"]]
        meeting_start = next_start
        meeting_end = meeting_start + next_meeting["duration"]

        itinerary.append({
            "action": "travel",
            "location": next_meeting["location"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(meeting_start)
        })

        itinerary.append({
            "action": "meet",
            "location": next_meeting["location"],
            "person": next_person,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })

        start_time = meeting_end
        current_location = next_meeting["location"]

    return itinerary

itinerary = find_meeting_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))