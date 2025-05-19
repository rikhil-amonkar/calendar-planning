import json
from datetime import datetime, timedelta
from itertools import permutations

# Travel distances (in minutes)
travel_times = {
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Sunset District"): 27,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Sunset District"): 23,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Sunset District"): 16,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Sunset District"): 19,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Sunset District"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Sunset District"): 29,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Presidio"): 16,
}

# Meeting constraints
meetings = [
    {"name": "Betty", "location": "Russian Hill", "start": "07:00", "end": "16:45", "duration": 105},
    {"name": "Melissa", "location": "Alamo Square", "start": "09:30", "end": "17:15", "duration": 105},
    {"name": "Joshua", "location": "Haight-Ashbury", "start": "12:15", "end": "19:00", "duration": 90},
    {"name": "Jeffrey", "location": "Marina District", "start": "12:15", "end": "18:00", "duration": 45},
    {"name": "James", "location": "Bayview", "start": "07:30", "end": "20:00", "duration": 90},
    {"name": "Anthony", "location": "Chinatown", "start": "11:45", "end": "13:30", "duration": 75},
    {"name": "Timothy", "location": "Presidio", "start": "12:30", "end": "14:45", "duration": 90},
    {"name": "Emily", "location": "Sunset District", "start": "19:30", "end": "21:30", "duration": 120},
]

def time_to_minutes(t):
    return int(t[:2]) * 60 + int(t[3:5])

def minutes_to_time(m):
    return f"{m // 60}:{m % 60:02d}"

def get_travel_time(from_loc, to_loc):
    return travel_times.get((from_loc, to_loc), travel_times.get((to_loc, from_loc), float('inf')))

def schedule_meetings(start_time, end_time, meetings):
    available_slots = []
    for meeting in meetings:
        start = time_to_minutes(meeting["start"])
        end = time_to_minutes(meeting["end"])
        available_slots.append((meeting["name"], meeting["location"], start, end, meeting["duration"]))

    best_itinerary = []
    max_meetings = 0

    for perm in permutations(available_slots):
        current_time = start_time
        current_itinerary = []
        valid_schedule = True

        for name, location, start, end, duration in perm:
            travel_time = get_travel_time("Union Square", location)
            start_meeting = max(current_time + travel_time, start)
            if start_meeting + duration > end:
                valid_schedule = False
                break
            
            current_itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": minutes_to_time(start_meeting),
                "end_time": minutes_to_time(start_meeting + duration)
            })
            current_time = start_meeting + duration + get_travel_time(location, "Union Square")

        if valid_schedule and len(current_itinerary) > max_meetings:
            max_meetings = len(current_itinerary)
            best_itinerary = current_itinerary

    return best_itinerary

# The day starts at 9:00 AM (9:00 in minutes)
start_time = time_to_minutes("09:00")
end_time = time_to_minutes("21:30")

itinerary = schedule_meetings(start_time, end_time, meetings)

result = {
    "itinerary": itinerary
}

print(json.dumps(result, indent=2))