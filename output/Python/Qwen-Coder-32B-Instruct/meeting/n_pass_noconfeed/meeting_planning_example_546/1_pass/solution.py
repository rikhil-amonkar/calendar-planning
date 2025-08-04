import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Bayview"): 21,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Bayview"): 26,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Bayview"): 15,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Bayview"): 19,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Bayview"): 22,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Bayview"): 19,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Nob Hill"): 20,
}

# Define meeting constraints
meetings = {
    "Kenneth": {"location": "Richmond District", "start": "21:15", "end": "22:00", "min_duration": 30},
    "Lisa": {"location": "Union Square", "start": "9:00", "end": "16:30", "min_duration": 45},
    "Joshua": {"location": "Financial District", "start": "12:00", "end": "15:15", "min_duration": 15},
    "Nancy": {"location": "Pacific Heights", "start": "8:00", "end": "11:30", "min_duration": 90},
    "Andrew": {"location": "Nob Hill", "start": "11:30", "end": "20:15", "min_duration": 60},
    "John": {"location": "Bayview", "start": "16:45", "end": "21:30", "min_duration": 75},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M")

def find_optimal_schedule():
    current_time = parse_time("9:00")
    current_location = "Embarcadero"
    itinerary = []

    # Sort meetings by earliest start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_meetings:
        location = details["location"]
        start = parse_time(details["start"])
        end = parse_time(details["end"])
        min_duration = details["min_duration"]

        # Calculate travel time to the next meeting location
        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Adjust arrival time if it's before the meeting start time
        if arrival_time < start:
            arrival_time = start

        # Calculate meeting end time
        meeting_end_time = arrival_time + timedelta(minutes=min_duration)

        # Check if the meeting can fit within the available time
        if meeting_end_time <= end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(arrival_time),
                "end_time": format_time(meeting_end_time)
            })
            current_time = meeting_end_time
            current_location = location
        else:
            # If the meeting cannot fit, skip it
            continue

    return itinerary

optimal_schedule = find_optimal_schedule()
result = {"itinerary": optimal_schedule}
print(json.dumps(result))