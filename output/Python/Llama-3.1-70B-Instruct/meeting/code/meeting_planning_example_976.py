import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "Embarcadero": {
        "Bayview": 21,
        "Chinatown": 7,
        "Alamo Square": 19,
        "Nob Hill": 10,
        "Presidio": 20,
        "Union Square": 10,
        "The Castro": 25,
        "North Beach": 5,
        "Fisherman's Wharf": 6,
        "Marina District": 12
    },
    "Bayview": {
        "Embarcadero": 19,
        "Chinatown": 19,
        "Alamo Square": 16,
        "Nob Hill": 20,
        "Presidio": 32,
        "Union Square": 18,
        "The Castro": 19,
        "North Beach": 22,
        "Fisherman's Wharf": 25,
        "Marina District": 27
    },
    "Chinatown": {
        "Embarcadero": 5,
        "Bayview": 20,
        "Alamo Square": 17,
        "Nob Hill": 9,
        "Presidio": 19,
        "Union Square": 7,
        "The Castro": 22,
        "North Beach": 3,
        "Fisherman's Wharf": 8,
        "Marina District": 12
    },
    "Alamo Square": {
        "Embarcadero": 16,
        "Bayview": 16,
        "Chinatown": 15,
        "Nob Hill": 11,
        "Presidio": 17,
        "Union Square": 14,
        "The Castro": 8,
        "North Beach": 15,
        "Fisherman's Wharf": 19,
        "Marina District": 15
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Bayview": 19,
        "Chinatown": 6,
        "Alamo Square": 11,
        "Presidio": 17,
        "Union Square": 7,
        "The Castro": 17,
        "North Beach": 8,
        "Fisherman's Wharf": 10,
        "Marina District": 11
    },
    "Presidio": {
        "Embarcadero": 20,
        "Bayview": 31,
        "Chinatown": 21,
        "Alamo Square": 19,
        "Nob Hill": 18,
        "Union Square": 22,
        "The Castro": 21,
        "North Beach": 18,
        "Fisherman's Wharf": 19,
        "Marina District": 11
    },
    "Union Square": {
        "Embarcadero": 11,
        "Bayview": 15,
        "Chinatown": 7,
        "Alamo Square": 15,
        "Nob Hill": 9,
        "Presidio": 24,
        "The Castro": 17,
        "North Beach": 10,
        "Fisherman's Wharf": 15,
        "Marina District": 18
    },
    "The Castro": {
        "Embarcadero": 22,
        "Bayview": 19,
        "Chinatown": 22,
        "Alamo Square": 8,
        "Nob Hill": 16,
        "Presidio": 20,
        "Union Square": 19,
        "North Beach": 20,
        "Fisherman's Wharf": 24,
        "Marina District": 21
    },
    "North Beach": {
        "Embarcadero": 6,
        "Bayview": 25,
        "Chinatown": 6,
        "Alamo Square": 16,
        "Nob Hill": 7,
        "Presidio": 17,
        "Union Square": 7,
        "The Castro": 23,
        "Fisherman's Wharf": 5,
        "Marina District": 9
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Bayview": 26,
        "Chinatown": 12,
        "Alamo Square": 21,
        "Nob Hill": 11,
        "Presidio": 17,
        "Union Square": 13,
        "The Castro": 27,
        "North Beach": 6,
        "Marina District": 10
    },
    "Marina District": {
        "Embarcadero": 14,
        "Bayview": 27,
        "Chinatown": 15,
        "Alamo Square": 15,
        "Nob Hill": 12,
        "Presidio": 10,
        "Union Square": 16,
        "The Castro": 22,
        "North Beach": 11,
        "Fisherman's Wharf": 10
    }
}

# Meeting constraints
meetings = [
    {"name": "Matthew", "location": "Bayview", "start_time": "19:15", "end_time": "22:00", "duration": 120},
    {"name": "Karen", "location": "Chinatown", "start_time": "19:15", "end_time": "21:15", "duration": 90},
    {"name": "Sarah", "location": "Alamo Square", "start_time": "20:00", "end_time": "21:45", "duration": 105},
    {"name": "Jessica", "location": "Nob Hill", "start_time": "16:30", "end_time": "18:45", "duration": 120},
    {"name": "Stephanie", "location": "Presidio", "start_time": "07:30", "end_time": "10:15", "duration": 60},
    {"name": "Mary", "location": "Union Square", "start_time": "16:45", "end_time": "21:30", "duration": 60},
    {"name": "Charles", "location": "The Castro", "start_time": "16:30", "end_time": "22:00", "duration": 105},
    {"name": "Nancy", "location": "North Beach", "start_time": "14:45", "end_time": "20:00", "duration": 15},
    {"name": "Thomas", "location": "Fisherman's Wharf", "start_time": "13:30", "end_time": "19:00", "duration": 30},
    {"name": "Brian", "location": "Marina District", "start_time": "12:15", "end_time": "18:00", "duration": 60}
]

def calculate_itinerary(meetings, travel_distances):
    itinerary = []
    current_location = "Embarcadero"
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