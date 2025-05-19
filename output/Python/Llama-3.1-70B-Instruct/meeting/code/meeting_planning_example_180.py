import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "North Beach": {
        "Mission District": 18,
        "The Castro": 22
    },
    "Mission District": {
        "North Beach": 17,
        "The Castro": 7
    },
    "The Castro": {
        "North Beach": 20,
        "Mission District": 7
    }
}

# Meeting constraints
meetings = [
    {"name": "James", "location": "Mission District", "start_time": "12:45", "end_time": "14:00", "duration": 75},
    {"name": "Robert", "location": "The Castro", "start_time": "12:45", "end_time": "15:15", "duration": 30}
]

def calculate_itinerary(meetings, travel_distances):
    itinerary = []
    current_location = "North Beach"
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