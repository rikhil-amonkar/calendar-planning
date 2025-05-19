import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "Union Square": {
        "Nob Hill": 9,
        "Haight-Ashbury": 18,
        "Chinatown": 7,
        "Marina District": 18
    },
    "Nob Hill": {
        "Union Square": 7,
        "Haight-Ashbury": 13,
        "Chinatown": 6,
        "Marina District": 11
    },
    "Haight-Ashbury": {
        "Union Square": 17,
        "Nob Hill": 15,
        "Chinatown": 19,
        "Marina District": 17
    },
    "Chinatown": {
        "Union Square": 7,
        "Nob Hill": 8,
        "Haight-Ashbury": 19,
        "Marina District": 12
    },
    "Marina District": {
        "Union Square": 16,
        "Nob Hill": 12,
        "Haight-Ashbury": 16,
        "Chinatown": 16
    }
}

# Meeting constraints
meetings = [
    {"name": "Karen", "location": "Nob Hill", "start_time": "21:15", "end_time": "21:45", "duration": 30},
    {"name": "Joseph", "location": "Haight-Ashbury", "start_time": "12:30", "end_time": "19:45", "duration": 90},
    {"name": "Sandra", "location": "Chinatown", "start_time": "07:15", "end_time": "19:15", "duration": 75},
    {"name": "Nancy", "location": "Marina District", "start_time": "11:00", "end_time": "20:15", "duration": 105}
]

def calculate_itinerary(meetings, travel_distances):
    itinerary = []
    current_location = "Union Square"
    current_time = datetime.strptime("09:00", "%H:%M")

    for meeting in meetings:
        travel_time = travel_distances[current_location][meeting["location"]]
        arrival_time = current_time + timedelta(minutes=travel_time)
        start_time = datetime.strptime(meeting["start_time"], "%H:%M")
        end_time = datetime.strptime(meeting["end_time"], "%H:%M")

        if arrival_time < start_time:
            wait_time = start_time - arrival_time
            current_time = start_time
        else:
            wait_time = timedelta(0)

        meeting_start_time = max(arrival_time, start_time)
        meeting_end_time = min(meeting_start_time + timedelta(minutes=meeting["duration"]), end_time)

        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["name"],
            "start_time": meeting_start_time.strftime("%H:%M"),
            "end_time": meeting_end_time.strftime("%H:%M")
        })

        current_time = meeting_end_time + wait_time + timedelta(minutes=travel_time)
        current_location = meeting["location"]

    return itinerary

itinerary = calculate_itinerary(meetings, travel_distances)
print(json.dumps({"itinerary": itinerary}, indent=4))