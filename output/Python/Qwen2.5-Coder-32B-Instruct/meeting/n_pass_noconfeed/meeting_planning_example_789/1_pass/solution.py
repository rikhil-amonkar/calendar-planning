import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    "Union Square": {
        "Russian Hill": 13, "Alamo Square": 15, "Haight-Ashbury": 18,
        "Marina District": 18, "Bayview": 15, "Chinatown": 7,
        "Presidio": 24, "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10, "Alamo Square": 13, "Haight-Ashbury": 17,
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

# Define the meeting constraints
constraints = {
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

def format_time(dt):
    return dt.strftime("%H:%M")

def can_meet(start, end, duration):
    return (parse_time(end) - parse_time(start)).total_seconds() / 60 >= duration

def find_meeting_schedule():
    current_location = "Union Square"
    current_time = parse_time("9:00")
    itinerary = []

    # Sort constraints by start time to prioritize earlier meetings
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]["start"]))

    for name, constraint in sorted_constraints:
        location = constraint["location"]
        start = parse_time(constraint["start"])
        end = parse_time(constraint["end"])
        min_duration = constraint["min_duration"]

        # Calculate travel time to the next location
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Check if we can meet the person for the required duration
        if arrival_time < start:
            meeting_start = start
        else:
            meeting_start = arrival_time

        meeting_end = meeting_start + timedelta(minutes=min_duration)

        if meeting_end <= end and meeting_start >= start:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
            current_time = meeting_end
            current_location = location
        else:
            # If we can't meet the person, skip this meeting
            continue

    return {"itinerary": itinerary}

# Generate the meeting schedule
schedule = find_meeting_schedule()

# Output the schedule as JSON
print(json.dumps(schedule))