import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Union Square"): 30,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Union Square"): 16,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Union Square"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Financial District"): 9,
}

# Define meeting constraints
meetings = {
    "Sarah": {"location": "Haight-Ashbury", "start": "17:00", "end": "21:30", "min_duration": 105},
    "Patricia": {"location": "Sunset District", "start": "17:00", "end": "19:45", "min_duration": 45},
    "Matthew": {"location": "Marina District", "start": "9:15", "end": "12:00", "min_duration": 15},
    "Joseph": {"location": "Financial District", "start": "14:15", "end": "18:45", "min_duration": 30},
    "Robert": {"location": "Union Square", "start": "10:15", "end": "21:45", "min_duration": 15},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M")

def can_meet(start, end, min_duration):
    duration = (end - start).total_seconds() / 60
    return duration >= min_duration

def find_optimal_schedule():
    current_time = parse_time("9:00")
    current_location = "Golden Gate Park"
    itinerary = []

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]["start"]))

    for name, details in sorted_meetings:
        location = details["location"]
        start = parse_time(details["start"])
        end = parse_time(details["end"])
        min_duration = details["min_duration"]

        # Calculate travel time
        travel_time = travel_times.get((current_location, location), float('inf'))
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Check if we can meet after traveling
        if arrival_time < start:
            meeting_start = start
        else:
            meeting_start = arrival_time

        meeting_end = meeting_start + timedelta(minutes=min_duration)

        # Check if meeting can fit within the person's availability
        if meeting_end <= end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
            current_time = meeting_end
            current_location = location

    return itinerary

optimal_schedule = find_optimal_schedule()
output = {"itinerary": optimal_schedule}
print(json.dumps(output))