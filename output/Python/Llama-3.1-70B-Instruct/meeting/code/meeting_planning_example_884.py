import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "Richmond District": {
        "Chinatown": 20,
        "Sunset District": 11,
        "Alamo Square": 13,
        "Financial District": 22,
        "North Beach": 17,
        "Embarcadero": 19,
        "Presidio": 7,
        "Golden Gate Park": 9,
        "Bayview": 27
    },
    "Chinatown": {
        "Richmond District": 20,
        "Sunset District": 29,
        "Alamo Square": 17,
        "Financial District": 5,
        "North Beach": 3,
        "Embarcadero": 5,
        "Presidio": 19,
        "Golden Gate Park": 23,
        "Bayview": 20
    },
    "Sunset District": {
        "Richmond District": 12,
        "Chinatown": 30,
        "Alamo Square": 17,
        "Financial District": 30,
        "North Beach": 28,
        "Embarcadero": 30,
        "Presidio": 16,
        "Golden Gate Park": 11,
        "Bayview": 22
    },
    "Alamo Square": {
        "Richmond District": 11,
        "Chinatown": 15,
        "Sunset District": 16,
        "Financial District": 17,
        "North Beach": 15,
        "Embarcadero": 16,
        "Presidio": 17,
        "Golden Gate Park": 9,
        "Bayview": 16
    },
    "Financial District": {
        "Richmond District": 21,
        "Chinatown": 5,
        "Sunset District": 30,
        "Alamo Square": 17,
        "North Beach": 7,
        "Embarcadero": 4,
        "Presidio": 22,
        "Golden Gate Park": 23,
        "Bayview": 19
    },
    "North Beach": {
        "Richmond District": 18,
        "Chinatown": 6,
        "Sunset District": 27,
        "Alamo Square": 16,
        "Financial District": 8,
        "Embarcadero": 6,
        "Presidio": 17,
        "Golden Gate Park": 22,
        "Bayview": 25
    },
    "Embarcadero": {
        "Richmond District": 21,
        "Chinatown": 7,
        "Sunset District": 30,
        "Alamo Square": 19,
        "Financial District": 5,
        "North Beach": 5,
        "Presidio": 20,
        "Golden Gate Park": 25,
        "Bayview": 21
    },
    "Presidio": {
        "Richmond District": 7,
        "Chinatown": 21,
        "Sunset District": 15,
        "Alamo Square": 19,
        "Financial District": 23,
        "North Beach": 18,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Bayview": 31
    },
    "Golden Gate Park": {
        "Richmond District": 7,
        "Chinatown": 23,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "North Beach": 23,
        "Embarcadero": 25,
        "Presidio": 11,
        "Bayview": 23
    },
    "Bayview": {
        "Richmond District": 25,
        "Chinatown": 19,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "North Beach": 22,
        "Embarcadero": 19,
        "Presidio": 32,
        "Golden Gate Park": 22
    }
}

# Meeting constraints
meetings = [
    {"name": "Robert", "location": "Chinatown", "start_time": "07:45", "end_time": "17:30", "duration": 120},
    {"name": "David", "location": "Sunset District", "start_time": "12:30", "end_time": "19:45", "duration": 45},
    {"name": "Matthew", "location": "Alamo Square", "start_time": "08:45", "end_time": "13:45", "duration": 90},
    {"name": "Jessica", "location": "Financial District", "start_time": "09:30", "end_time": "18:45", "duration": 45},
    {"name": "Melissa", "location": "North Beach", "start_time": "07:15", "end_time": "16:45", "duration": 45},
    {"name": "Mark", "location": "Embarcadero", "start_time": "15:15", "end_time": "17:00", "duration": 45},
    {"name": "Deborah", "location": "Presidio", "start_time": "19:00", "end_time": "19:45", "duration": 45},
    {"name": "Karen", "location": "Golden Gate Park", "start_time": "19:30", "end_time": "22:00", "duration": 120},
    {"name": "Laura", "location": "Bayview", "start_time": "21:15", "end_time": "22:15", "duration": 15}
]

def calculate_itinerary(meetings, travel_distances):
    itinerary = []
    current_location = "Richmond District"
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