import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "Union Square": {
        "Mission District": 14,
        "Fisherman's Wharf": 15,
        "Russian Hill": 13,
        "Marina District": 18,
        "North Beach": 10,
        "Chinatown": 7,
        "Pacific Heights": 15,
        "The Castro": 17,
        "Nob Hill": 9,
        "Sunset District": 27
    },
    "Mission District": {
        "Union Square": 15,
        "Fisherman's Wharf": 22,
        "Russian Hill": 15,
        "Marina District": 19,
        "North Beach": 17,
        "Chinatown": 16,
        "Pacific Heights": 16,
        "The Castro": 7,
        "Nob Hill": 12,
        "Sunset District": 24
    },
    "Fisherman's Wharf": {
        "Union Square": 13,
        "Mission District": 22,
        "Russian Hill": 7,
        "Marina District": 9,
        "North Beach": 6,
        "Chinatown": 12,
        "Pacific Heights": 12,
        "The Castro": 27,
        "Nob Hill": 11,
        "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10,
        "Mission District": 16,
        "Fisherman's Wharf": 7,
        "Marina District": 7,
        "North Beach": 5,
        "Chinatown": 9,
        "Pacific Heights": 7,
        "The Castro": 21,
        "Nob Hill": 5,
        "Sunset District": 23
    },
    "Marina District": {
        "Union Square": 16,
        "Mission District": 20,
        "Fisherman's Wharf": 10,
        "Russian Hill": 8,
        "North Beach": 11,
        "Chinatown": 15,
        "Pacific Heights": 7,
        "The Castro": 22,
        "Nob Hill": 12,
        "Sunset District": 19
    },
    "North Beach": {
        "Union Square": 7,
        "Mission District": 18,
        "Fisherman's Wharf": 5,
        "Russian Hill": 4,
        "Marina District": 9,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 23,
        "Nob Hill": 7,
        "Sunset District": 27
    },
    "Chinatown": {
        "Union Square": 7,
        "Mission District": 17,
        "Fisherman's Wharf": 8,
        "Russian Hill": 7,
        "Marina District": 12,
        "North Beach": 3,
        "Pacific Heights": 10,
        "The Castro": 22,
        "Nob Hill": 9,
        "Sunset District": 29
    },
    "Pacific Heights": {
        "Union Square": 12,
        "Mission District": 15,
        "Fisherman's Wharf": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "North Beach": 9,
        "Chinatown": 11,
        "The Castro": 16,
        "Nob Hill": 8,
        "Sunset District": 21
    },
    "The Castro": {
        "Union Square": 19,
        "Mission District": 7,
        "Fisherman's Wharf": 24,
        "Russian Hill": 18,
        "Marina District": 21,
        "North Beach": 20,
        "Chinatown": 22,
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Sunset District": 17
    },
    "Nob Hill": {
        "Union Square": 7,
        "Mission District": 13,
        "Fisherman's Wharf": 10,
        "Russian Hill": 5,
        "Marina District": 11,
        "North Beach": 8,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 17,
        "Sunset District": 24
    },
    "Sunset District": {
        "Union Square": 30,
        "Mission District": 25,
        "Fisherman's Wharf": 29,
        "Russian Hill": 24,
        "Marina District": 21,
        "North Beach": 28,
        "Chinatown": 30,
        "Pacific Heights": 21,
        "The Castro": 17,
        "Nob Hill": 27
    }
}

# Meeting constraints
meetings = [
    {"name": "Kevin", "location": "Mission District", "start_time": "20:45", "end_time": "21:45", "duration": 60},
    {"name": "Mark", "location": "Fisherman's Wharf", "start_time": "17:15", "end_time": "20:00", "duration": 90},
    {"name": "Jessica", "location": "Russian Hill", "start_time": "09:00", "end_time": "15:00", "duration": 120},
    {"name": "Jason", "location": "Marina District", "start_time": "15:15", "end_time": "21:45", "duration": 120},
    {"name": "John", "location": "North Beach", "start_time": "09:45", "end_time": "18:00", "duration": 15},
    {"name": "Karen", "location": "Chinatown", "start_time": "16:45", "end_time": "19:00", "duration": 75},
    {"name": "Sarah", "location": "Pacific Heights", "start_time": "17:30", "end_time": "18:15", "duration": 45},
    {"name": "Amanda", "location": "The Castro", "start_time": "20:00", "end_time": "21:15", "duration": 60},
    {"name": "Nancy", "location": "Nob Hill", "start_time": "09:45", "end_time": "13:00", "duration": 45},
    {"name": "Rebecca", "location": "Sunset District", "start_time": "08:45", "end_time": "15:00", "duration": 75}
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