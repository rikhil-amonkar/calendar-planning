import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "Marina District": {
        "Richmond District": 11,
        "Union Square": 16,
        "Nob Hill": 12,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Financial District": 17,
        "North Beach": 11,
        "Presidio": 10
    },
    "Richmond District": {
        "Marina District": 9,
        "Union Square": 21,
        "Nob Hill": 17,
        "Fisherman's Wharf": 18,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Financial District": 22,
        "North Beach": 17,
        "Presidio": 7
    },
    "Union Square": {
        "Marina District": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Fisherman's Wharf": 15,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Financial District": 9,
        "North Beach": 10,
        "Presidio": 24
    },
    "Nob Hill": {
        "Marina District": 11,
        "Richmond District": 14,
        "Union Square": 7,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Financial District": 9,
        "North Beach": 8,
        "Presidio": 17
    },
    "Fisherman's Wharf": {
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 13,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Financial District": 11,
        "North Beach": 6,
        "Presidio": 17
    },
    "Golden Gate Park": {
        "Marina District": 16,
        "Richmond District": 7,
        "Union Square": 22,
        "Nob Hill": 20,
        "Fisherman's Wharf": 24,
        "Embarcadero": 25,
        "Financial District": 26,
        "North Beach": 23,
        "Presidio": 11
    },
    "Embarcadero": {
        "Marina District": 12,
        "Richmond District": 21,
        "Union Square": 10,
        "Nob Hill": 10,
        "Fisherman's Wharf": 6,
        "Golden Gate Park": 25,
        "Financial District": 5,
        "North Beach": 5,
        "Presidio": 20
    },
    "Financial District": {
        "Marina District": 15,
        "Richmond District": 21,
        "Union Square": 9,
        "Nob Hill": 8,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "North Beach": 7,
        "Presidio": 22
    },
    "North Beach": {
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 7,
        "Nob Hill": 7,
        "Fisherman's Wharf": 5,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Financial District": 8,
        "Presidio": 17
    },
    "Presidio": {
        "Marina District": 11,
        "Richmond District": 7,
        "Union Square": 22,
        "Nob Hill": 18,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Financial District": 23,
        "North Beach": 18
    }
}

# Meeting constraints
meetings = [
    {"name": "Stephanie", "location": "Richmond District", "start_time": "16:15", "end_time": "21:30", "duration": 75},
    {"name": "William", "location": "Union Square", "start_time": "10:45", "end_time": "17:30", "duration": 45},
    {"name": "Elizabeth", "location": "Nob Hill", "start_time": "12:15", "end_time": "15:00", "duration": 105},
    {"name": "Joseph", "location": "Fisherman's Wharf", "start_time": "12:45", "end_time": "14:00", "duration": 75},
    {"name": "Anthony", "location": "Golden Gate Park", "start_time": "13:00", "end_time": "20:30", "duration": 75},
    {"name": "Barbara", "location": "Embarcadero", "start_time": "19:15", "end_time": "20:30", "duration": 75},
    {"name": "Carol", "location": "Financial District", "start_time": "11:45", "end_time": "16:15", "duration": 60},
    {"name": "Sandra", "location": "North Beach", "start_time": "10:00", "end_time": "12:30", "duration": 15},
    {"name": "Kenneth", "location": "Presidio", "start_time": "21:15", "end_time": "22:15", "duration": 45}
]

def calculate_itinerary(meetings, travel_distances):
    itinerary = []
    current_location = "Marina District"
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