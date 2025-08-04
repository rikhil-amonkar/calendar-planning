import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "North Beach"): 24,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "North Beach"): 3,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "North Beach"): 10,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "North Beach"): 9,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
}

# Define meeting constraints
meetings = {
    "Stephanie": {"location": "Golden Gate Park", "start": "11:00", "end": "15:00", "min_duration": 105},
    "Karen": {"location": "Chinatown", "start": "13:45", "end": "16:30", "min_duration": 15},
    "Brian": {"location": "Union Square", "start": "15:00", "end": "17:15", "min_duration": 30},
    "Rebecca": {"location": "Fisherman's Wharf", "start": "8:00", "end": "11:15", "min_duration": 30},
    "Joseph": {"location": "Pacific Heights", "start": "8:15", "end": "9:30", "min_duration": 60},
    "Steven": {"location": "North Beach", "start": "14:30", "end": "20:45", "min_duration": 120},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%H:%M")

def find_optimal_schedule():
    current_location = "Financial District"
    current_time = parse_time("9:00")
    itinerary = []

    def can_meet(person, start_time, end_time, min_duration):
        person_start = parse_time(meetings[person]["start"])
        person_end = parse_time(meetings[person]["end"])
        available_start = max(start_time, person_start)
        available_end = min(end_time, person_end)
        return (available_end - available_start).total_seconds() / 60 >= min_duration

    def add_meeting(person, start_time, end_time):
        location = meetings[person]["location"]
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": format_time(start_time),
            "end_time": format_time(end_time)
        })

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]["start"]))

    for person, details in sorted_meetings:
        location = details["location"]
        min_duration = details["min_duration"]

        # Calculate travel time
        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Check if we can meet within constraints
        if can_meet(person, arrival_time, parse_time(details["end"]), min_duration):
            meeting_start_time = max(arrival_time, parse_time(details["start"]))
            meeting_end_time = meeting_start_time + timedelta(minutes=min_duration)
            add_meeting(person, meeting_start_time, meeting_end_time)
            current_time = meeting_end_time
            current_location = location

    return itinerary

itinerary = find_optimal_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))