import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "North Beach": {
        "Pacific Heights": 8,
        "Embarcadero": 6
    },
    "Pacific Heights": {
        "North Beach": 9,
        "Embarcadero": 10
    },
    "Embarcadero": {
        "North Beach": 5,
        "Pacific Heights": 11
    }
}

# Meeting constraints
meetings = [
    {"name": "Karen", "location": "Pacific Heights", "start_time": "18:45", "end_time": "20:15", "duration": 90},
    {"name": "Mark", "location": "Embarcadero", "start_time": "13:00", "end_time": "17:45", "duration": 120}
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