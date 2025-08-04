import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Haight-Ashbury": {"Russian Hill": 17, "Fisherman's Wharf": 23, "Nob Hill": 15, "Golden Gate Park": 7, "Alamo Square": 5, "Pacific Heights": 12},
    "Russian Hill": {"Haight-Ashbury": 17, "Fisherman's Wharf": 7, "Nob Hill": 5, "Golden Gate Park": 21, "Alamo Square": 15, "Pacific Heights": 7},
    "Fisherman's Wharf": {"Haight-Ashbury": 22, "Russian Hill": 7, "Nob Hill": 11, "Golden Gate Park": 25, "Alamo Square": 20, "Pacific Heights": 12},
    "Nob Hill": {"Haight-Ashbury": 13, "Russian Hill": 5, "Fisherman's Wharf": 11, "Golden Gate Park": 17, "Alamo Square": 11, "Pacific Heights": 8},
    "Golden Gate Park": {"Haight-Ashbury": 7, "Russian Hill": 19, "Fisherman's Wharf": 24, "Nob Hill": 20, "Alamo Square": 10, "Pacific Heights": 16},
    "Alamo Square": {"Haight-Ashbury": 5, "Russian Hill": 13, "Fisherman's Wharf": 19, "Nob Hill": 11, "Golden Gate Park": 9, "Pacific Heights": 10},
    "Pacific Heights": {"Haight-Ashbury": 11, "Russian Hill": 7, "Fisherman's Wharf": 13, "Nob Hill": 8, "Golden Gate Park": 15, "Alamo Square": 10}
}

# Define meeting constraints
constraints = {
    "Stephanie": {"location": "Russian Hill", "start": "20:00", "end": "20:45", "min_duration": 15},
    "Kevin": {"location": "Fisherman's Wharf", "start": "19:15", "end": "21:45", "min_duration": 75},
    "Robert": {"location": "Nob Hill", "start": "07:45", "end": "10:30", "min_duration": 90},
    "Steven": {"location": "Golden Gate Park", "start": "08:30", "end": "17:00", "min_duration": 75},
    "Anthony": {"location": "Alamo Square", "start": "07:45", "end": "19:45", "min_duration": 15},
    "Sandra": {"location": "Pacific Heights", "start": "14:45", "end": "21:45", "min_duration": 45}
}

def time_to_minutes(time_str):
    return int(time_str.split(':')[0]) * 60 + int(time_str.split(':')[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02d}"

def can_meet(start_time, end_time, min_duration):
    return (time_to_minutes(end_time) - time_to_minutes(start_time)) >= min_duration

def find_optimal_schedule():
    start_location = "Haight-Ashbury"
    start_time = "09:00"
    current_time = time_to_minutes(start_time)
    current_location = start_location
    itinerary = []

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: time_to_minutes(x[1]['start']))

    for person, details in sorted_constraints:
        location = details["location"]
        start = details["start"]  # Ensure this remains a string
        end = details["end"]      # Ensure this remains a string
        min_duration = details["min_duration"]

        # Calculate travel time to the next location
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time

        # Check if we can meet the person within their availability
        if arrival_time <= time_to_minutes(start):
            meeting_start = time_to_minutes(start)
        elif time_to_minutes(start) <= arrival_time <= time_to_minutes(end):
            meeting_start = arrival_time
        else:
            continue

        meeting_end = meeting_start + min_duration

        # Ensure meeting does not exceed person's availability
        if meeting_end > time_to_minutes(end):
            meeting_end = time_to_minutes(end)

        # Ensure meeting duration meets minimum requirement
        if can_meet(minutes_to_time(meeting_start), minutes_to_time(meeting_end), min_duration):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = location

    return itinerary

optimal_schedule = find_optimal_schedule()
output = {"itinerary": optimal_schedule}
print(json.dumps(output, indent=4))