import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 29,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4
}

# Define meeting constraints
meetings = {
    "Anthony": {"location": "Chinatown", "start": "13:15", "end": "14:30", "min_duration": 60},
    "Rebecca": {"location": "Russian Hill", "start": "19:30", "end": "21:15", "min_duration": 105},
    "Melissa": {"location": "North Beach", "start": "8:15", "end": "13:30", "min_duration": 105}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M")

def find_meeting_schedule():
    start_time = parse_time("9:00")
    current_location = "Sunset District"
    itinerary = []

    def can_meet(meeting, start):
        meeting_start = parse_time(meeting["start"])
        meeting_end = parse_time(meeting["end"])
        return start <= meeting_end - timedelta(minutes=meeting["min_duration"])

    def add_meeting_to_itinerary(person, location, start, duration):
        end = start + timedelta(minutes=duration)
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": format_time(start),
            "end_time": format_time(end)
        })
        return end

    # Try to meet Melissa first if possible
    melissa_meeting = meetings["Melissa"]
    if can_meet(melissa_meeting, start_time):
        travel_time = travel_times[(current_location, melissa_meeting["location"])]
        start_time += timedelta(minutes=travel_time)
        start_time = max(start_time, parse_time(melissa_meeting["start"]))
        start_time = add_meeting_to_itinerary("Melissa", melissa_meeting["location"], start_time, melissa_meeting["min_duration"])
        current_location = melissa_meeting["location"]

    # Try to meet Anthony next if possible
    anthony_meeting = meetings["Anthony"]
    if can_meet(anthony_meeting, start_time):
        travel_time = travel_times[(current_location, anthony_meeting["location"])]
        start_time += timedelta(minutes=travel_time)
        start_time = max(start_time, parse_time(anthony_meeting["start"]))
        start_time = add_meeting_to_itinerary("Anthony", anthony_meeting["location"], start_time, anthony_meeting["min_duration"])
        current_location = anthony_meeting["location"]

    # Finally, try to meet Rebecca if possible
    rebecca_meeting = meetings["Rebecca"]
    if can_meet(rebecca_meeting, start_time):
        travel_time = travel_times[(current_location, rebecca_meeting["location"])]
        start_time += timedelta(minutes=travel_time)
        start_time = max(start_time, parse_time(rebecca_meeting["start"]))
        add_meeting_to_itinerary("Rebecca", rebecca_meeting["location"], start_time, rebecca_meeting["min_duration"])

    return itinerary

itinerary = find_meeting_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))