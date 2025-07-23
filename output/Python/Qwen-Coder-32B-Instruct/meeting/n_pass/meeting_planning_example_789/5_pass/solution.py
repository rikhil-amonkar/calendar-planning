import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Union Square": {
        "Russian Hill": 13, "Alamo Square": 15, "Haight-Ashbury": 18,
        "Marina District": 18, "Bayview": 15, "Chinatown": 7,
        "Presidio": 24, "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10, "Alamo Square": 15, "Haight-Ashbury": 17,
        "Marina District": 7, "Bayview": 23, "Chinatown": 9,
        "Presidio": 14, "Sunset District": 23
    },
    "Alamo Square": {
        "Union Square": 14, "Russian Hill": 13, "Haight-Ashbury": 5,
        "Marina District": 15, "Bayview": 16, "Chinatown": 15,
        "Presidio": 17, "Sunset District": 16
    },
    "Haight-Ashbury": {
        "Union Square": 19, "Russian Hill": 17, "Alamo Square": 5,
        "Marina District": 17, "Bayview": 18, "Chinatown": 19,
        "Presidio": 15, "Sunset District": 15
    },
    "Marina District": {
        "Union Square": 16, "Russian Hill": 8, "Alamo Square": 15,
        "Haight-Ashbury": 16, "Bayview": 27, "Chinatown": 15,
        "Presidio": 10, "Sunset District": 19
    },
    "Bayview": {
        "Union Square": 18, "Russian Hill": 23, "Alamo Square": 16,
        "Haight-Ashbury": 19, "Marina District": 27, "Chinatown": 19,
        "Presidio": 32, "Sunset District": 23
    },
    "Chinatown": {
        "Union Square": 7, "Russian Hill": 7, "Alamo Square": 17,
        "Haight-Ashbury": 19, "Marina District": 12, "Bayview": 20,
        "Presidio": 19, "Sunset District": 29
    },
    "Presidio": {
        "Union Square": 22, "Russian Hill": 14, "Alamo Square": 19,
        "Haight-Ashbury": 15, "Marina District": 11, "Bayview": 31,
        "Chinatown": 21, "Sunset District": 15
    },
    "Sunset District": {
        "Union Square": 30, "Russian Hill": 24, "Alamo Square": 17,
        "Haight-Ashbury": 15, "Marina District": 21, "Bayview": 22,
        "Chinatown": 30, "Presidio": 16
    }
}

# Define meeting constraints
meetings = {
    "Betty": {"location": "Russian Hill", "start": "7:00", "end": "16:45", "min_duration": 105},
    "Melissa": {"location": "Alamo Square", "start": "9:30", "end": "17:15", "min_duration": 105},
    "Joshua": {"location": "Haight-Ashbury", "start": "12:15", "end": "19:00", "min_duration": 90},
    "Jeffrey": {"location": "Marina District", "start": "12:15", "end": "18:00", "min_duration": 45},
    "James": {"location": "Bayview", "start": "7:30", "end": "20:00", "min_duration": 90},
    "Anthony": {"location": "Chinatown", "start": "11:45", "end": "13:30", "min_duration": 75},
    "Timothy": {"location": "Presidio", "start": "12:30", "end": "14:45", "min_duration": 90},
    "Emily": {"location": "Sunset District", "start": "19:30", "end": "21:30", "min_duration": 120}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_to_str(dt):
    return dt.strftime("%H:%M")

def find_meeting_schedule():
    current_time = parse_time("9:00")
    current_location = "Union Square"
    itinerary = []

    def can_meet(person, start_time, end_time, min_duration):
        travel_time = travel_times[current_location][meetings[person]["location"]]
        available_start = max(start_time, current_time + timedelta(minutes=travel_time))
        available_end = min(end_time, parse_time(meetings[person]["end"]))
        return (available_end - available_start).total_seconds() / 60 >= min_duration

    def meet(person, start_time, end_time, min_duration):
        nonlocal current_time, current_location
        travel_time = travel_times[current_location][meetings[person]["location"]]
        arrival_time = current_time + timedelta(minutes=travel_time)
        if arrival_time < start_time:
            arrival_time = start_time
        leave_time = arrival_time + timedelta(minutes=min_duration)
        if leave_time > end_time:
            leave_time = end_time
        itinerary.append({
            "action": "meet",
            "location": meetings[person]["location"],
            "person": person,
            "start_time": time_to_str(arrival_time),
            "end_time": time_to_str(leave_time)
        })
        current_time = leave_time
        current_location = meetings[person]["location"]

    # Sort meetings by earliest possible start time after travel
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]["start"]) + timedelta(minutes=travel_times[current_location][x[1]["location"]]))

    for person, details in sorted_meetings:
        start_time = parse_time(details["start"])
        end_time = parse_time(details["end"])
        min_duration = details["min_duration"]
        if can_meet(person, start_time, end_time, min_duration):
            meet(person, start_time, end_time, min_duration)

    return itinerary

itinerary = find_meeting_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result, indent=4))