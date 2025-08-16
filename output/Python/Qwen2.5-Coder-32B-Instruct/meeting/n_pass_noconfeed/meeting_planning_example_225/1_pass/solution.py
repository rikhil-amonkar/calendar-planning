import json
from datetime import datetime, timedelta

# Define travel times
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
    ("Alamo Square", "Union Square"): 14,
}

# Define constraints
constraints = {
    "Sarah": {"location": "North Beach", "start": "16:00", "end": "18:15", "min_duration": 60},
    "Jeffrey": {"location": "Union Square", "start": "15:00", "end": "22:00", "min_duration": 75},
    "Brian": {"location": "Alamo Square", "start": "16:00", "end": "17:30", "min_duration": 75},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_to_str(time_obj):
    return time_obj.strftime("%H:%M")

def find_meeting_time(constraint, current_time):
    start = max(parse_time(constraint["start"]), current_time)
    end = parse_time(constraint["end"])
    if (end - start).total_seconds() / 60 >= constraint["min_duration"]:
        return start, start + timedelta(minutes=constraint["min_duration"])
    return None, None

def calculate_schedule():
    current_location = "Sunset District"
    current_time = parse_time("9:00")
    itinerary = []

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]["start"]))

    for person, constraint in sorted_constraints:
        location = constraint["location"]
        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + timedelta(minutes=travel_time)

        start_time, end_time = find_meeting_time(constraint, arrival_time)
        if start_time:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": time_to_str(start_time),
                "end_time": time_to_str(end_time)
            })
            current_time = end_time
            current_location = location

    return itinerary

schedule = calculate_schedule()
result = {"itinerary": schedule}
print(json.dumps(result))