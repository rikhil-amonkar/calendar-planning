import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "Fisherman's Wharf": {
        "Bayview": 26,
        "Golden Gate Park": 25,
        "Nob Hill": 11,
        "Marina District": 9,
        "Embarcadero": 8
    },
    "Bayview": {
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22,
        "Nob Hill": 20,
        "Marina District": 25,
        "Embarcadero": 19
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Nob Hill": 20,
        "Marina District": 16,
        "Embarcadero": 25
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11,
        "Bayview": 19,
        "Golden Gate Park": 17,
        "Marina District": 11,
        "Embarcadero": 9
    },
    "Marina District": {
        "Fisherman's Wharf": 10,
        "Bayview": 27,
        "Golden Gate Park": 18,
        "Nob Hill": 12,
        "Embarcadero": 14
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Bayview": 21,
        "Golden Gate Park": 25,
        "Nob Hill": 10,
        "Marina District": 12
    }
}

# Meeting constraints
meetings = [
    {"name": "Thomas", "location": "Bayview", "start_time": "15:30", "end_time": "18:30", "duration": 120},
    {"name": "Stephanie", "location": "Golden Gate Park", "start_time": "18:30", "end_time": "21:45", "duration": 30},
    {"name": "Laura", "location": "Nob Hill", "start_time": "08:45", "end_time": "16:15", "duration": 30},
    {"name": "Betty", "location": "Marina District", "start_time": "18:45", "end_time": "21:45", "duration": 45},
    {"name": "Patricia", "location": "Embarcadero", "start_time": "17:30", "end_time": "22:00", "duration": 45}
]

def calculate_itinerary(meetings, travel_distances):
    itinerary = []
    current_location = "Fisherman's Wharf"
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