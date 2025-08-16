import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7,
}

# Define meeting constraints
meetings = {
    "Stephanie": {"location": "Mission District", "start": "8:15", "end": "13:45", "min_duration": 90},
    "Sandra": {"location": "Bayview", "start": "13:00", "end": "19:30", "min_duration": 15},
    "Richard": {"location": "Pacific Heights", "start": "7:15", "end": "10:15", "min_duration": 75},
    "Brian": {"location": "Russian Hill", "start": "12:15", "end": "16:00", "min_duration": 120},
    "Jason": {"location": "Fisherman's Wharf", "start": "8:30", "end": "17:45", "min_duration": 60},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_to_str(time_obj):
    return time_obj.strftime("%H:%M").lstrip('0')

def find_meeting_schedule(start_time, meetings, travel_times):
    itinerary = []
    current_location = "Haight-Ashbury"
    current_time = start_time

    def can_meet(meeting, current_time):
        meeting_start = parse_time(meeting["start"])
        meeting_end = parse_time(meeting["end"])
        min_duration = timedelta(minutes=meeting["min_duration"])
        return meeting_start <= current_time + min_duration <= meeting_end

    def find_next_meeting(current_time, current_location):
        next_meeting = None
        for person, meeting in meetings.items():
            if can_meet(meeting, current_time):
                location = meeting["location"]
                travel_time = travel_times[(current_location, location)]
                arrival_time = current_time + timedelta(minutes=travel_time)
                if can_meet(meeting, arrival_time):
                    if next_meeting is None or arrival_time < next_meeting[0]:
                        next_meeting = (arrival_time, location, person)
        return next_meeting

    while meetings:
        next_meeting = find_next_meeting(current_time, current_location)
        if next_meeting is None:
            break
        arrival_time, location, person = next_meeting
        meeting_start = arrival_time
        meeting_end = parse_time(meetings[person]["end"])
        min_duration = timedelta(minutes=meetings[person]["min_duration"])
        meeting_end = max(meeting_start + min_duration, meeting_end - min_duration)
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": time_to_str(meeting_start),
            "end_time": time_to_str(meeting_end)
        })
        current_time = meeting_end + timedelta(minutes=travel_times[(location, current_location)])
        current_location = "Haight-Ashbury"
        del meetings[person]

    return itinerary

start_time = parse_time("9:00")
itinerary = find_meeting_schedule(start_time, meetings.copy(), travel_times)

print(json.dumps({"itinerary": itinerary}, indent=2))