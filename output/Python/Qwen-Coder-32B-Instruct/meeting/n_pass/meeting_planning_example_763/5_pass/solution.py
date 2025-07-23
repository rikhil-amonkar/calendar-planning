import json
from datetime import datetime, timedelta

# Define the travel times
travel_times = {
    ("Chinatown", "Embarcadero"): 5, ("Chinatown", "Pacific Heights"): 10, ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Haight-Ashbury"): 19, ("Chinatown", "Golden Gate Park"): 23, ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Sunset District"): 29, ("Chinatown", "The Castro"): 22, ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Pacific Heights"): 11, ("Embarcadero", "Russian Hill"): 8, ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Golden Gate Park"): 25, ("Embarcadero", "Fisherman's Wharf"): 6, ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "The Castro"): 25, ("Pacific Heights", "Chinatown"): 11, ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Russian Hill"): 7, ("Pacific Heights", "Haight-Ashbury"): 11, ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13, ("Pacific Heights", "Sunset District"): 21, ("Pacific Heights", "The Castro"): 16,
    ("Russian Hill", "Chinatown"): 9, ("Russian Hill", "Embarcadero"): 8, ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17, ("Russian Hill", "Golden Gate Park"): 21, ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Sunset District"): 23, ("Russian Hill", "The Castro"): 21, ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20, ("Haight-Ashbury", "Pacific Heights"): 12, ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Golden Gate Park"): 7, ("Haight-Ashbury", "Fisherman's Wharf"): 23, ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "The Castro"): 6, ("Golden Gate Park", "Chinatown"): 23, ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Pacific Heights"): 16, ("Golden Gate Park", "Russian Hill"): 19, ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24, ("Golden Gate Park", "Sunset District"): 10, ("Golden Gate Park", "The Castro"): 13,
    ("Fisherman's Wharf", "Chinatown"): 12, ("Fisherman's Wharf", "Embarcadero"): 8, ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7, ("Fisherman's Wharf", "Haight-Ashbury"): 22, ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Sunset District"): 27, ("Fisherman's Wharf", "The Castro"): 27, ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Embarcadero"): 30, ("Sunset District", "Pacific Heights"): 21, ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Haight-Ashbury"): 15, ("Sunset District", "Golden Gate Park"): 11, ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "The Castro"): 17, ("The Castro", "Chinatown"): 22, ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Pacific Heights"): 16, ("The Castro", "Russian Hill"): 18, ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Golden Gate Park"): 11, ("The Castro", "Fisherman's Wharf"): 24, ("The Castro", "Sunset District"): 17
}

# Define the meeting constraints
constraints = {
    "Richard": {"location": "Embarcadero", "start": "15:15", "end": "18:45", "min_duration": 90},
    "Mark": {"location": "Pacific Heights", "start": "15:00", "end": "17:00", "min_duration": 45},
    "Matthew": {"location": "Russian Hill", "start": "17:30", "end": "21:00", "min_duration": 90},
    "Rebecca": {"location": "Haight-Ashbury", "start": "14:45", "end": "18:00", "min_duration": 60},
    "Melissa": {"location": "Golden Gate Park", "start": "13:45", "end": "17:30", "min_duration": 90},
    "Margaret": {"location": "Fisherman's Wharf", "start": "14:45", "end": "20:15", "min_duration": 15},
    "Emily": {"location": "Sunset District", "start": "15:45", "end": "17:00", "min_duration": 45},
    "George": {"location": "The Castro", "start": "14:00", "end": "16:15", "min_duration": 75}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%H:%M")

def can_meet(start, end, duration):
    return (parse_time(end) - parse_time(start)).total_seconds() / 60 >= duration

def find_schedule():
    current_location = "Chinatown"
    current_time = parse_time("9:00")
    itinerary = []

    def add_meeting(person, location, start, end, duration):
        nonlocal current_time, current_location
        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + timedelta(minutes=travel_time)
        if arrival_time >= parse_time(end):
            return False  # Cannot arrive on time
        meeting_start = max(arrival_time, parse_time(start))
        meeting_end = meeting_start + timedelta(minutes=duration)
        if meeting_end <= parse_time(end):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
            current_time = meeting_end
            current_location = location
            return True
        return False

    # Sort constraints by earliest possible start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_constraints:
        if can_meet(details['start'], details['end'], details['min_duration']):
            if add_meeting(person, details['location'], details['start'], details['end'], details['min_duration']):
                continue

    return {"itinerary": itinerary}

schedule = find_schedule()
print(json.dumps(schedule, indent=2))