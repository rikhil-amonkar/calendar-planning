import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "Bayview": {
        "North Beach": 22,
        "Fisherman's Wharf": 25,
        "Haight-Ashbury": 19,
        "Nob Hill": 20,
        "Golden Gate Park": 22,
        "Union Square": 18,
        "Alamo Square": 16,
        "Presidio": 32,
        "Chinatown": 19,
        "Pacific Heights": 23
    },
    "North Beach": {
        "Bayview": 25,
        "Fisherman's Wharf": 5,
        "Haight-Ashbury": 18,
        "Nob Hill": 7,
        "Golden Gate Park": 22,
        "Union Square": 7,
        "Alamo Square": 16,
        "Presidio": 17,
        "Chinatown": 6,
        "Pacific Heights": 8
    },
    "Fisherman's Wharf": {
        "Bayview": 26,
        "North Beach": 6,
        "Haight-Ashbury": 22,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Union Square": 13,
        "Alamo Square": 21,
        "Presidio": 17,
        "Chinatown": 12,
        "Pacific Heights": 12
    },
    "Haight-Ashbury": {
        "Bayview": 18,
        "North Beach": 19,
        "Fisherman's Wharf": 23,
        "Nob Hill": 15,
        "Golden Gate Park": 7,
        "Union Square": 19,
        "Alamo Square": 5,
        "Presidio": 15,
        "Chinatown": 19,
        "Pacific Heights": 12
    },
    "Nob Hill": {
        "Bayview": 19,
        "North Beach": 8,
        "Fisherman's Wharf": 10,
        "Haight-Ashbury": 13,
        "Golden Gate Park": 17,
        "Union Square": 7,
        "Alamo Square": 11,
        "Presidio": 17,
        "Chinatown": 6,
        "Pacific Heights": 8
    },
    "Golden Gate Park": {
        "Bayview": 23,
        "North Beach": 23,
        "Fisherman's Wharf": 24,
        "Haight-Ashbury": 7,
        "Nob Hill": 20,
        "Union Square": 22,
        "Alamo Square": 9,
        "Presidio": 11,
        "Chinatown": 23,
        "Pacific Heights": 16
    },
    "Union Square": {
        "Bayview": 15,
        "North Beach": 10,
        "Fisherman's Wharf": 15,
        "Haight-Ashbury": 18,
        "Nob Hill": 9,
        "Golden Gate Park": 22,
        "Alamo Square": 15,
        "Presidio": 24,
        "Chinatown": 7,
        "Pacific Heights": 15
    },
    "Alamo Square": {
        "Bayview": 16,
        "North Beach": 15,
        "Fisherman's Wharf": 19,
        "Haight-Ashbury": 5,
        "Nob Hill": 11,
        "Golden Gate Park": 9,
        "Union Square": 14,
        "Presidio": 17,
        "Chinatown": 15,
        "Pacific Heights": 10
    },
    "Presidio": {
        "Bayview": 31,
        "North Beach": 18,
        "Fisherman's Wharf": 19,
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "Golden Gate Park": 12,
        "Union Square": 22,
        "Alamo Square": 19,
        "Chinatown": 21,
        "Pacific Heights": 11
    },
    "Chinatown": {
        "Bayview": 20,
        "North Beach": 3,
        "Fisherman's Wharf": 8,
        "Haight-Ashbury": 19,
        "Nob Hill": 9,
        "Golden Gate Park": 23,
        "Union Square": 7,
        "Alamo Square": 17,
        "Presidio": 19,
        "Pacific Heights": 11
    },
    "Pacific Heights": {
        "Bayview": 22,
        "North Beach": 9,
        "Fisherman's Wharf": 13,
        "Haight-Ashbury": 11,
        "Nob Hill": 8,
        "Golden Gate Park": 15,
        "Union Square": 12,
        "Alamo Square": 10,
        "Presidio": 11,
        "Chinatown": 11
    }
}

# Meeting constraints
meetings = [
    {"name": "Brian", "location": "North Beach", "start_time": "13:00", "end_time": "19:00", "duration": 90},
    {"name": "Richard", "location": "Fisherman's Wharf", "start_time": "11:00", "end_time": "12:45", "duration": 60},
    {"name": "Ashley", "location": "Haight-Ashbury", "start_time": "15:00", "end_time": "20:30", "duration": 90},
    {"name": "Elizabeth", "location": "Nob Hill", "start_time": "11:45", "end_time": "18:30", "duration": 75},
    {"name": "Jessica", "location": "Golden Gate Park", "start_time": "20:00", "end_time": "21:45", "duration": 105},
    {"name": "Deborah", "location": "Union Square", "start_time": "17:30", "end_time": "22:00", "duration": 60},
    {"name": "Kimberly", "location": "Alamo Square", "start_time": "17:30", "end_time": "21:15", "duration": 45},
    {"name": "Matthew", "location": "Presidio", "start_time": "08:15", "end_time": "09:00", "duration": 15},
    {"name": "Kenneth", "location": "Chinatown", "start_time": "13:45", "end_time": "19:30", "duration": 105},
    {"name": "Anthony", "location": "Pacific Heights", "start_time": "14:15", "end_time": "16:00", "duration": 30}
]

def calculate_itinerary(meetings, travel_distances):
    itinerary = []
    current_location = "Bayview"
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