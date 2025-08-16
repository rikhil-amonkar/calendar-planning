import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Mission District": {
        "The Castro": 7, "Nob Hill": 12, "Presidio": 25, "Marina District": 19,
        "Pacific Heights": 16, "Golden Gate Park": 17, "Chinatown": 16, "Richmond District": 20
    },
    "The Castro": {
        "Mission District": 7, "Nob Hill": 16, "Presidio": 20, "Marina District": 21,
        "Pacific Heights": 16, "Golden Gate Park": 11, "Chinatown": 22, "Richmond District": 16
    },
    "Nob Hill": {
        "Mission District": 13, "The Castro": 17, "Presidio": 17, "Marina District": 11,
        "Pacific Heights": 8, "Golden Gate Park": 17, "Chinatown": 6, "Richmond District": 14
    },
    "Presidio": {
        "Mission District": 26, "The Castro": 21, "Nob Hill": 18, "Marina District": 10,
        "Pacific Heights": 11, "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7
    },
    "Marina District": {
        "Mission District": 20, "The Castro": 22, "Nob Hill": 12, "Presidio": 10,
        "Pacific Heights": 6, "Golden Gate Park": 18, "Chinatown": 15, "Richmond District": 11
    },
    "Pacific Heights": {
        "Mission District": 15, "The Castro": 16, "Nob Hill": 8, "Presidio": 11,
        "Marina District": 6, "Golden Gate Park": 15, "Chinatown": 11, "Richmond District": 12
    },
    "Golden Gate Park": {
        "Mission District": 17, "The Castro": 13, "Nob Hill": 20, "Presidio": 11,
        "Marina District": 16, "Pacific Heights": 16, "Chinatown": 23, "Richmond District": 7
    },
    "Chinatown": {
        "Mission District": 17, "The Castro": 22, "Nob Hill": 9, "Presidio": 19,
        "Marina District": 12, "Pacific Heights": 10, "Golden Gate Park": 23, "Richmond District": 20
    },
    "Richmond District": {
        "Mission District": 20, "The Castro": 16, "Nob Hill": 17, "Presidio": 7,
        "Marina District": 9, "Pacific Heights": 10, "Golden Gate Park": 9, "Chinatown": 20
    }
}

# Define meeting constraints
meetings = {
    "Lisa": {"location": "The Castro", "start": "19:15", "end": "21:15", "min_duration": 120},
    "Daniel": {"location": "Nob Hill", "start": "8:15", "end": "11:00", "min_duration": 15},
    "Elizabeth": {"location": "Presidio", "start": "21:15", "end": "22:15", "min_duration": 45},
    "Steven": {"location": "Marina District", "start": "16:30", "end": "20:45", "min_duration": 90},
    "Timothy": {"location": "Pacific Heights", "start": "12:00", "end": "18:00", "min_duration": 90},
    "Ashley": {"location": "Golden Gate Park", "start": "20:45", "end": "21:45", "min_duration": 60},
    "Kevin": {"location": "Chinatown", "start": "12:00", "end": "19:00", "min_duration": 30},
    "Betty": {"location": "Richmond District", "start": "13:15", "end": "15:45", "min_duration": 30}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M")

def can_meet(current_time, start, end, min_duration):
    start_time = parse_time(start)
    end_time = parse_time(end)
    return start_time <= current_time <= end_time and (end_time - current_time).total_seconds() / 60 >= min_duration

def find_optimal_schedule():
    current_time = parse_time("9:00")
    current_location = "Mission District"
    itinerary = []

    def add_meeting(person, location, start, end, min_duration):
        nonlocal current_time, current_location
        start_time = parse_time(start)
        end_time = parse_time(end)
        
        # Calculate travel time
        travel_time = travel_times[current_location][location]
        potential_start_time = current_time + timedelta(minutes=travel_time)
        
        # Check if we can start the meeting within the person's available time
        if potential_start_time < start_time:
            potential_start_time = start_time
        
        # Check if the meeting can fit within the person's available time
        if can_meet(potential_start_time, start, end, min_duration):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(potential_start_time),
                "end_time": format_time(min(potential_start_time + timedelta(minutes=min_duration), end_time))
            })
            current_time = potential_start_time + timedelta(minutes=min_duration)
            current_location = location
            return True
        else:
            return False

    # Prioritize meetings based on constraints
    meetings_order = sorted(meetings.items(), key=lambda x: (parse_time(x[1]['start']), -x[1]['min_duration']))

    for person, details in meetings_order:
        if not add_meeting(person, details['location'], details['start'], details['end'], details['min_duration']):
            print(f"Skipping meeting with {person} as it cannot be scheduled within their availability.")

    return itinerary

itinerary = find_optimal_schedule()
output = {"itinerary": itinerary}
print(json.dumps(output))