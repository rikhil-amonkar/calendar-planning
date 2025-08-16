import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Alamo Square"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Union Square"): 14
}

# Define constraints
constraints = {
    "Sarah": {"location": "North Beach", "start": "16:00", "end": "18:15", "min_duration": 60},
    "Jeffrey": {"location": "Union Square", "start": "15:00", "end": "22:00", "min_duration": 75},
    "Brian": {"location": "Alamo Square", "start": "16:00", "end": "17:30", "min_duration": 75}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_meeting_schedule(constraints, travel_times):
    start_time = parse_time("9:00")
    current_location = "Sunset District"
    itinerary = []

    def try_meeting(person, location, start, end, min_duration):
        nonlocal start_time, current_location, itinerary
        travel_time = travel_times[(current_location, location)]
        arrival_time = add_minutes(start_time, travel_time)
        if arrival_time < start:
            meeting_start = start
        else:
            meeting_start = arrival_time
        meeting_end = add_minutes(meeting_start, min_duration)
        if meeting_end <= end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start.strftime("%H:%M"),
                "end_time": meeting_end.strftime("%H:%M")
            })
            start_time = meeting_end
            current_location = location
            return True
        return False

    # Try to meet Jeffrey first due to longer availability
    if try_meeting("Jeffrey", constraints["Jeffrey"]["location"], 
                   parse_time(constraints["Jeffrey"]["start"]), 
                   parse_time(constraints["Jeffrey"]["end"]), 
                   constraints["Jeffrey"]["min_duration"]):
        # Try to meet Sarah next
        try_meeting("Sarah", constraints["Sarah"]["location"], 
                    parse_time(constraints["Sarah"]["start"]), 
                    parse_time(constraints["Sarah"]["end"]), 
                    constraints["Sarah"]["min_duration"])
        # Try to meet Brian last
        try_meeting("Brian", constraints["Brian"]["location"], 
                    parse_time(constraints["Brian"]["start"]), 
                    parse_time(constraints["Brian"]["end"]), 
                    constraints["Brian"]["min_duration"])

    return itinerary

itinerary = find_meeting_schedule(constraints, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result))