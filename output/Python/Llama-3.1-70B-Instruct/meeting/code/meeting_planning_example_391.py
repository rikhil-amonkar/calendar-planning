import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "Sunset District": {
        "Alamo Square": 17,
        "Russian Hill": 24,
        "Presidio": 16,
        "Financial District": 30
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Russian Hill": 13,
        "Presidio": 18,
        "Financial District": 17
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Alamo Square": 15,
        "Presidio": 14,
        "Financial District": 11
    },
    "Presidio": {
        "Sunset District": 15,
        "Alamo Square": 18,
        "Russian Hill": 14,
        "Financial District": 23
    },
    "Financial District": {
        "Sunset District": 31,
        "Alamo Square": 17,
        "Russian Hill": 10,
        "Presidio": 22
    }
}

# Meeting constraints
meetings = [
    {"name": "Kevin", "location": "Alamo Square", "start_time": "08:15", "end_time": "21:30", "duration": 75},
    {"name": "Kimberly", "location": "Russian Hill", "start_time": "08:45", "end_time": "12:30", "duration": 30},
    {"name": "Joseph", "location": "Presidio", "start_time": "18:30", "end_time": "19:15", "duration": 45},
    {"name": "Thomas", "location": "Financial District", "start_time": "19:00", "end_time": "21:45", "duration": 45}
]

def calculate_itinerary(meetings, travel_distances):
    itinerary = []
    current_location = "Sunset District"
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