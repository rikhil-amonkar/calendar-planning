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
        "Mission District": 26, "The Castro": 21, "Nob Hill": 18, "Marina District": 11,
        "Pacific Heights": 11, "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7
    },
    "Marina District": {
        "Mission District": 20, "The Castro": 22, "Nob Hill": 12, "Presidio": 10,
        "Pacific Heights": 7, "Golden Gate Park": 18, "Chinatown": 15, "Richmond District": 11
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
constraints = {
    "Lisa": {"location": "The Castro", "start": "19:15", "end": "21:15", "duration": 120},
    "Daniel": {"location": "Nob Hill", "start": "8:15", "end": "11:00", "duration": 15},
    "Elizabeth": {"location": "Presidio", "start": "21:15", "end": "22:15", "duration": 45},
    "Steven": {"location": "Marina District", "start": "16:30", "end": "20:45", "duration": 90},
    "Timothy": {"location": "Pacific Heights", "start": "12:00", "end": "18:00", "duration": 90},
    "Ashley": {"location": "Golden Gate Park", "start": "20:45", "end": "21:45", "duration": 60},
    "Kevin": {"location": "Chinatown", "start": "12:00", "end": "19:00", "duration": 30},
    "Betty": {"location": "Richmond District", "start": "13:15", "end": "15:45", "duration": 30}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_diff(start, end):
    return int((end - start).total_seconds() / 60)

def can_meet(start, end, duration):
    return time_diff(start, end) >= duration

def find_schedule(constraints, travel_times):
    current_location = "Mission District"
    current_time = parse_time("9:00")
    itinerary = []

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]["start"]))

    for person, constraint in sorted_constraints:
        location = constraint["location"]
        start_time = parse_time(constraint["start"])
        end_time = parse_time(constraint["end"])
        duration = constraint["duration"]

        # Calculate travel time to the next location
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Check if we can meet the person after traveling
        if arrival_time <= start_time and can_meet(arrival_time, end_time, duration):
            meeting_start = max(arrival_time, start_time)
            meeting_end = meeting_start + timedelta(minutes=duration)

            # Add to itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start.strftime("%H:%M"),
                "end_time": meeting_end.strftime("%H:%M")
            })

            # Update current location and time
            current_location = location
            current_time = meeting_end

    return itinerary

itinerary = find_schedule(constraints, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result))