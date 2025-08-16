import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Presidio": {
        "Pacific Heights": 11, "Golden Gate Park": 12, "Fisherman's Wharf": 19,
        "Marina District": 11, "Alamo Square": 19, "Sunset District": 15,
        "Nob Hill": 18, "North Beach": 18
    },
    "Pacific Heights": {
        "Presidio": 11, "Golden Gate Park": 15, "Fisherman's Wharf": 13,
        "Marina District": 6, "Alamo Square": 10, "Sunset District": 21,
        "Nob Hill": 8, "North Beach": 9
    },
    "Golden Gate Park": {
        "Presidio": 11, "Pacific Heights": 16, "Fisherman's Wharf": 24,
        "Marina District": 16, "Alamo Square": 9, "Sunset District": 10,
        "Nob Hill": 20, "North Beach": 23
    },
    "Fisherman's Wharf": {
        "Presidio": 17, "Pacific Heights": 12, "Golden Gate Park": 25,
        "Marina District": 9, "Alamo Square": 21, "Sunset District": 27,
        "Nob Hill": 11, "North Beach": 6
    },
    "Marina District": {
        "Presidio": 10, "Pacific Heights": 7, "Golden Gate Park": 18,
        "Fisherman's Wharf": 10, "Alamo Square": 15, "Sunset District": 19,
        "Nob Hill": 12, "North Beach": 11
    },
    "Alamo Square": {
        "Presidio": 17, "Pacific Heights": 10, "Golden Gate Park": 9,
        "Fisherman's Wharf": 19, "Marina District": 15, "Sunset District": 16,
        "Nob Hill": 11, "North Beach": 15
    },
    "Sunset District": {
        "Presidio": 16, "Pacific Heights": 21, "Golden Gate Park": 11,
        "Fisherman's Wharf": 29, "Marina District": 21, "Alamo Square": 17,
        "Nob Hill": 27, "North Beach": 28
    },
    "Nob Hill": {
        "Presidio": 17, "Pacific Heights": 8, "Golden Gate Park": 17,
        "Fisherman's Wharf": 10, "Marina District": 11, "Alamo Square": 11,
        "Sunset District": 24, "North Beach": 8
    },
    "North Beach": {
        "Presidio": 17, "Pacific Heights": 8, "Golden Gate Park": 22,
        "Fisherman's Wharf": 5, "Marina District": 9, "Alamo Square": 16,
        "Sunset District": 27, "Nob Hill": 7
    }
}

# Define meeting constraints
constraints = {
    "Kevin": {"location": "Pacific Heights", "start": "7:15", "end": "8:45", "min_duration": 90},
    "Michelle": {"location": "Golden Gate Park", "start": "20:00", "end": "21:00", "min_duration": 15},
    "Emily": {"location": "Fisherman's Wharf", "start": "16:15", "end": "19:00", "min_duration": 30},
    "Mark": {"location": "Marina District", "start": "18:15", "end": "19:45", "min_duration": 75},
    "Barbara": {"location": "Alamo Square", "start": "17:00", "end": "19:00", "min_duration": 120},
    "Laura": {"location": "Sunset District", "start": "19:00", "end": "21:15", "min_duration": 75},
    "Mary": {"location": "Nob Hill", "start": "17:30", "end": "19:00", "min_duration": 45},
    "Helen": {"location": "North Beach", "start": "11:00", "end": "12:15", "min_duration": 45}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_to_minutes(time):
    return time.hour * 60 + time.minute

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

def find_meeting_schedule(constraints, travel_times):
    start_time = parse_time("9:00")
    current_location = "Presidio"
    itinerary = []

    def can_meet(start, end, min_duration):
        duration = (parse_time(end) - parse_time(start)).total_seconds() / 60
        return duration >= min_duration

    def add_meeting(person, location, start, end):
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": start,
            "end_time": end
        })

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]["start"]))

    for person, details in sorted_constraints:
        location = details["location"]
        start = details["start"]
        end = details["end"]
        min_duration = details["min_duration"]

        if can_meet(start, end, min_duration):
            travel_time = travel_times[current_location][location]
            arrival_time = start_time + timedelta(minutes=travel_time)

            # Ensure we can arrive on time and have enough time for the meeting
            if arrival_time <= parse_time(start):
                meeting_start = arrival_time
            elif parse_time(start) + timedelta(minutes=min_duration) <= parse_time(end):
                meeting_start = parse_time(start)
            else:
                continue

            meeting_end = meeting_start + timedelta(minutes=min_duration)

            if meeting_end <= parse_time(end):
                add_meeting(person, location, minutes_to_time(time_to_minutes(meeting_start)), minutes_to_time(time_to_minutes(meeting_end)))
                current_location = location
                start_time = meeting_end

    return itinerary

itinerary = find_meeting_schedule(constraints, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result, indent=4))