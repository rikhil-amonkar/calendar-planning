import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes_val):
    hours = minutes_val // 60
    minutes = minutes_val % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Sunset District": 10,
        "Marina District": 16,
        "Financial District": 26,
        "Union Square": 22
    },
    "Haight-Ashbury": {
        "Golden Gate Park": 7,
        "Sunset District": 15,
        "Marina District": 17,
        "Financial District": 21,
        "Union Square": 17
    },
    "Sunset District": {
        "Golden Gate Park": 11,
        "Haight-Ashbury": 15,
        "Marina District": 21,
        "Financial District": 30,
        "Union Square": 30
    },
    "Marina District": {
        "Golden Gate Park": 18,
        "Haight-Ashbury": 16,
        "Sunset District": 19,
        "Financial District": 17,
        "Union Square": 16
    },
    "Financial District": {
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Sunset District": 31,
        "Marina District": 15,
        "Union Square": 9
    },
    "Union Square": {
        "Golden Gate Park": 22,
        "Haight-Ashbury": 18,
        "Sunset District": 26,
        "Marina District": 18,
        "Financial District": 9
    }
}

friends = [
    {"name": "Matthew", "location": "Marina District", "available_start": "9:15", "available_end": "12:00", "min_duration": 15},
    {"name": "Robert", "location": "Union Square", "available_start": "10:15", "available_end": "21:45", "min_duration": 15},
    {"name": "Joseph", "location": "Financial District", "available_start": "14:15", "available_end": "18:45", "min_duration": 30},
    {"name": "Sarah", "location": "Haight-Ashbury", "available_start": "17:00", "available_end": "21:30", "min_duration": 105},
    {"name": "Patricia", "location": "Sunset District", "available_start": "17:00", "available_end": "19:45", "min_duration": 45}
]

current_time = time_to_minutes("9:00")
current_location = "Golden Gate Park"
itinerary = []

for friend in friends:
    travel_time = travel_times[current_location][friend["location"]]
    arrival_time = current_time + travel_time
    available_start = time_to_minutes(friend["available_start"])
    available_end = time_to_minutes(friend["available_end"])
    start_meeting = max(arrival_time, available_start)
    if start_meeting + friend["min_duration"] <= available_end:
        end_meeting = start_meeting + friend["min_duration"]
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(start_meeting),
            "end_time": minutes_to_time(end_meeting)
        })
        current_time = end_meeting
        current_location = friend["location"]
    else:
        current_time = arrival_time
        current_location = friend["location"]

print(json.dumps({"itinerary": itinerary}))