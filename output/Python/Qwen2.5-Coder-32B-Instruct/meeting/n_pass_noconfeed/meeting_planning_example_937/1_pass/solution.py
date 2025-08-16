import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Russian Hill": {
        "Sunset District": 23, "Union Square": 10, "Nob Hill": 5, "Marina District": 7,
        "Richmond District": 14, "Financial District": 11, "Embarcadero": 8, "The Castro": 21,
        "Alamo Square": 15, "Presidio": 14
    },
    "Sunset District": {
        "Russian Hill": 24, "Union Square": 30, "Nob Hill": 27, "Marina District": 21,
        "Richmond District": 12, "Financial District": 30, "Embarcadero": 30, "The Castro": 17,
        "Alamo Square": 17, "Presidio": 16
    },
    "Union Square": {
        "Russian Hill": 13, "Sunset District": 27, "Nob Hill": 9, "Marina District": 18,
        "Richmond District": 20, "Financial District": 9, "Embarcadero": 11, "The Castro": 17,
        "Alamo Square": 15, "Presidio": 24
    },
    "Nob Hill": {
        "Russian Hill": 5, "Sunset District": 24, "Union Square": 7, "Marina District": 11,
        "Richmond District": 14, "Financial District": 9, "Embarcadero": 9, "The Castro": 17,
        "Alamo Square": 11, "Presidio": 17
    },
    "Marina District": {
        "Russian Hill": 8, "Sunset District": 19, "Union Square": 16, "Nob Hill": 12,
        "Richmond District": 11, "Financial District": 17, "Embarcadero": 14, "The Castro": 22,
        "Alamo Square": 15, "Presidio": 10
    },
    "Richmond District": {
        "Russian Hill": 13, "Sunset District": 11, "Union Square": 21, "Nob Hill": 17,
        "Marina District": 9, "Financial District": 22, "Embarcadero": 19, "The Castro": 16,
        "Alamo Square": 13, "Presidio": 7
    },
    "Financial District": {
        "Russian Hill": 11, "Sunset District": 30, "Union Square": 9, "Nob Hill": 8,
        "Marina District": 15, "Richmond District": 21, "Embarcadero": 4, "The Castro": 20,
        "Alamo Square": 17, "Presidio": 22
    },
    "Embarcadero": {
        "Russian Hill": 8, "Sunset District": 30, "Union Square": 10, "Nob Hill": 10,
        "Marina District": 12, "Richmond District": 21, "Financial District": 5, "The Castro": 25,
        "Alamo Square": 19, "Presidio": 20
    },
    "The Castro": {
        "Russian Hill": 18, "Sunset District": 17, "Union Square": 19, "Nob Hill": 16,
        "Marina District": 21, "Richmond District": 16, "Financial District": 21, "Embarcadero": 22,
        "Alamo Square": 8, "Presidio": 20
    },
    "Alamo Square": {
        "Russian Hill": 13, "Sunset District": 16, "Union Square": 14, "Nob Hill": 11,
        "Marina District": 15, "Richmond District": 11, "Financial District": 17, "Embarcadero": 16,
        "The Castro": 8, "Presidio": 17
    },
    "Presidio": {
        "Russian Hill": 14, "Sunset District": 15, "Union Square": 22, "Nob Hill": 18,
        "Marina District": 11, "Richmond District": 7, "Financial District": 23, "Embarcadero": 20,
        "The Castro": 21, "Alamo Square": 19
    }
}

# Define meeting constraints
meetings = {
    "David": {"location": "Sunset District", "start": "9:15", "end": "22:00", "duration": 15},
    "Kenneth": {"location": "Union Square", "start": "21:15", "end": "21:45", "duration": 15},
    "Patricia": {"location": "Nob Hill", "start": "15:00", "end": "19:15", "duration": 120},
    "Mary": {"location": "Marina District", "start": "14:45", "end": "16:45", "duration": 45},
    "Charles": {"location": "Richmond District", "start": "17:15", "end": "21:00", "duration": 15},
    "Joshua": {"location": "Financial District", "start": "14:30", "end": "17:15", "duration": 90},
    "Ronald": {"location": "Embarcadero", "start": "18:15", "end": "20:45", "duration": 30},
    "George": {"location": "The Castro", "start": "14:15", "end": "19:00", "duration": 105},
    "Kimberly": {"location": "Alamo Square", "start": "9:00", "end": "14:30", "duration": 105},
    "William": {"location": "Presidio", "start": "7:00", "end": "12:45", "duration": 60}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M")

def can_meet(start, end, duration):
    return (end - start).total_seconds() / 60 >= duration

def find_meeting_schedule():
    start_time = parse_time("9:00")
    current_location = "Russian Hill"
    itinerary = []

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for name, details in sorted_meetings:
        location = details['location']
        start = parse_time(details['start'])
        end = parse_time(details['end'])
        duration = details['duration']

        # Calculate travel time
        travel_time = travel_times[current_location][location]
        arrival_time = start_time + timedelta(minutes=travel_time)

        # Check if we can meet within the constraints
        if arrival_time <= start and can_meet(arrival_time, end, duration):
            meeting_start = arrival_time
            meeting_end = meeting_start + timedelta(minutes=duration)
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
            start_time = meeting_end
            current_location = location

    return {"itinerary": itinerary}

schedule = find_meeting_schedule()
print(json.dumps(schedule))