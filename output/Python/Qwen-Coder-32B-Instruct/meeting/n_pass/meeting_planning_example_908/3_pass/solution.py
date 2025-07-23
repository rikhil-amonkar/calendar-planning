import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Financial District": {
        "Fisherman's Wharf": 10, "Presidio": 22, "Bayview": 19, "Haight-Ashbury": 19,
        "Russian Hill": 11, "The Castro": 20, "Marina District": 15, "Richmond District": 21,
        "Union Square": 9, "Sunset District": 30,
        "Bayview": 19, "The Castro": 20, "Haight-Ashbury": 19, "Sunset District": 30
    },
    "Fisherman's Wharf": {
        "Financial District": 11, "Presidio": 17, "Bayview": 26, "Haight-Ashbury": 22,
        "Russian Hill": 7, "The Castro": 27, "Marina District": 9, "Richmond District": 18,
        "Union Square": 13, "Sunset District": 27,
        "Bayview": 26, "The Castro": 27, "Haight-Ashbury": 22, "Sunset District": 27
    },
    "Presidio": {
        "Financial District": 23, "Fisherman's Wharf": 19, "Bayview": 31, "Haight-Ashbury": 15,
        "Russian Hill": 14, "The Castro": 21, "Marina District": 11, "Richmond District": 7,
        "Union Square": 22, "Sunset District": 15,
        "Bayview": 31, "The Castro": 21, "Haight-Ashbury": 15, "Sunset District": 15
    },
    "Bayview": {
        "Financial District": 19, "Fisherman's Wharf": 25, "Presidio": 32, "Haight-Ashbury": 19,
        "Russian Hill": 23, "The Castro": 19, "Marina District": 27, "Richmond District": 25,
        "Union Square": 18, "Sunset District": 23,
        "Financial District": 19, "Fisherman's Wharf": 25, "Presidio": 32, "Haight-Ashbury": 19,
        "Russian Hill": 23, "The Castro": 19, "Marina District": 27, "Richmond District": 25,
        "Union Square": 18, "Sunset District": 23
    },
    "Haight-Ashbury": {
        "Financial District": 21, "Fisherman's Wharf": 23, "Presidio": 15, "Bayview": 18,
        "Russian Hill": 17, "The Castro": 6, "Marina District": 17, "Richmond District": 10,
        "Union Square": 19, "Sunset District": 15,
        "Financial District": 21, "Fisherman's Wharf": 23, "Presidio": 15, "Bayview": 18,
        "Russian Hill": 17, "The Castro": 6, "Marina District": 17, "Richmond District": 10,
        "Union Square": 19, "Sunset District": 15
    },
    "Russian Hill": {
        "Financial District": 11, "Fisherman's Wharf": 7, "Presidio": 14, "Bayview": 23,
        "Haight-Ashbury": 17, "The Castro": 21, "Marina District": 7, "Richmond District": 14,
        "Union Square": 10, "Sunset District": 23,
        "Financial District": 11, "Fisherman's Wharf": 7, "Presidio": 14, "Bayview": 23,
        "Haight-Ashbury": 17, "The Castro": 21, "Marina District": 7, "Richmond District": 14,
        "Union Square": 10, "Sunset District": 23
    },
    "The Castro": {
        "Financial District": 21, "Fisherman's Wharf": 24, "Presidio": 20, "Bayview": 19,
        "Haight-Ashbury": 6, "Russian Hill": 18, "Marina District": 22, "Richmond District": 16,
        "Union Square": 19, "Sunset District": 17,
        "Financial District": 21, "Fisherman's Wharf": 24, "Presidio": 20, "Bayview": 19,
        "Haight-Ashbury": 6, "Russian Hill": 18, "Marina District": 22, "Richmond District": 16,
        "Union Square": 19, "Sunset District": 17
    },
    "Marina District": {
        "Financial District": 17, "Fisherman's Wharf": 10, "Presidio": 10, "Bayview": 27,
        "Haight-Ashbury": 16, "Russian Hill": 8, "The Castro": 22, "Richmond District": 11,
        "Union Square": 16, "Sunset District": 19,
        "Financial District": 17, "Fisherman's Wharf": 10, "Presidio": 10, "Bayview": 27,
        "Haight-Ashbury": 16, "Russian Hill": 8, "The Castro": 22, "Richmond District": 11,
        "Union Square": 16, "Sunset District": 19
    },
    "Richmond District": {
        "Financial District": 22, "Fisherman's Wharf": 18, "Presidio": 7, "Bayview": 27,
        "Haight-Ashbury": 10, "Russian Hill": 13, "The Castro": 16, "Marina District": 9,
        "Union Square": 21, "Sunset District": 11,
        "Financial District": 22, "Fisherman's Wharf": 18, "Presidio": 7, "Bayview": 27,
        "Haight-Ashbury": 10, "Russian Hill": 13, "The Castro": 16, "Marina District": 9,
        "Union Square": 21, "Sunset District": 11
    },
    "Union Square": {
        "Financial District": 9, "Fisherman's Wharf": 15, "Presidio": 24, "Bayview": 15,
        "Haight-Ashbury": 18, "Russian Hill": 13, "The Castro": 17, "Marina District": 18,
        "Richmond District": 20, "Sunset District": 27,
        "Financial District": 9, "Fisherman's Wharf": 15, "Presidio": 24, "Bayview": 15,
        "Haight-Ashbury": 18, "Russian Hill": 13, "The Castro": 17, "Marina District": 18,
        "Richmond District": 20, "Sunset District": 27
    },
    "Sunset District": {
        "Financial District": 30, "Fisherman's Wharf": 29, "Presidio": 16, "Bayview": 22,
        "Haight-Ashbury": 15, "Russian Hill": 24, "The Castro": 17, "Marina District": 21,
        "Richmond District": 12, "Union Square": 30,
        "Financial District": 30, "Fisherman's Wharf": 29, "Presidio": 16, "Bayview": 22,
        "Haight-Ashbury": 15, "Russian Hill": 24, "The Castro": 17, "Marina District": 21,
        "Richmond District": 12, "Union Square": 30
    }
}

# Define meeting constraints
meetings = {
    "Mark": {"location": "Fisherman's Wharf", "start": "8:15", "end": "10:00", "min_duration": 30},
    "Stephanie": {"location": "Presidio", "start": "12:15", "end": "15:00", "min_duration": 75},
    "Betty": {"location": "Bayview", "start": "7:15", "end": "20:30", "min_duration": 15},
    "Lisa": {"location": "Haight-Ashbury", "start": "15:30", "end": "18:30", "min_duration": 45},
    "William": {"location": "Russian Hill", "start": "18:45", "end": "20:00", "min_duration": 60},
    "Brian": {"location": "The Castro", "start": "9:15", "end": "13:15", "min_duration": 30},
    "Joseph": {"location": "Marina District", "start": "10:45", "end": "15:00", "min_duration": 90},
    "Ashley": {"location": "Richmond District", "start": "9:45", "end": "11:15", "min_duration": 45},
    "Patricia": {"location": "Union Square", "start": "16:30", "end": "20:00", "min_duration": 120},
    "Karen": {"location": "Sunset District", "start": "16:30", "end": "22:00", "min_duration": 105}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M").lstrip('0')

def can_meet(start, end, min_duration, current_time):
    start_time = parse_time(start)
    end_time = parse_time(end)
    if current_time >= start_time and current_time <= end_time - timedelta(minutes=min_duration):
        return True
    return False

def find_next_meeting(current_location, current_time):
    available_meetings = []
    for person, details in meetings.items():
        if can_meet(details["start"], details["end"], details["min_duration"], current_time):
            try:
                travel_time = travel_times[current_location][details["location"]]
                potential_start = current_time + timedelta(minutes=travel_time)
                if potential_start + timedelta(minutes=details["min_duration"]) <= parse_time(details["end"]):
                    available_meetings.append((person, details["location"], potential_start))
            except KeyError as e:
                print(f"KeyError: {e} - current_location: {current_location}, details['location']: {details['location']}")
    if available_meetings:
        available_meetings.sort(key=lambda x: x[2])
        return available_meetings[0]
    return None

def create_schedule():
    itinerary = []
    current_location = "Financial District"
    current_time = parse_time("9:00")
    
    while True:
        next_meeting = find_next_meeting(current_location, current_time)
        if not next_meeting:
            break
        person, location, start_time = next_meeting
        details = meetings[person]
        end_time = start_time + timedelta(minutes=details["min_duration"])
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": format_time(start_time),
            "end_time": format_time(end_time)
        })
        current_location = location
        current_time = end_time
    
    return itinerary

schedule = create_schedule()
result = {"itinerary": schedule}
print(json.dumps(result, indent=2))