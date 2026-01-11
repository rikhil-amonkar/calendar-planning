import json
from datetime import datetime, timedelta

# Constants
START_TIME = 9 * 60  # 9:00 AM in minutes
END_OF_DAY = 21 * 60  # 9:00 PM in minutes

# Locations and travel times
locations = ["Embarcadero", "Presidio", "Richmond District", "Fisherman's Wharf"]
travel_times = {
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
}

# Friends' availability and meeting durations
friends = {
    "Betty": {"location": "Presidio", "start": 10 * 60 + 15, "end": 21 * 60 + 30, "min_duration": 45},
    "David": {"location": "Richmond District", "start": 13 * 60, "end": 20 * 60 + 15, "min_duration": 90},
    "Barbara": {"location": "Fisherman's Wharf", "start": 9 * 60 + 15, "end": 20 * 60 + 15, "min_duration": 120},
}

def time_to_str(minutes):
    return str(datetime(1, 1, 1) + timedelta(minutes=minutes)).split()[1][:5]

def find_best_schedule(current_location, current_time, visited_friends, itinerary):
    if len(visited_friends) == len(friends):
        return itinerary, current_time

    best_itinerary = None
    best_end_time = END_OF_DAY

    for friend, details in friends.items():
        if friend in visited_friends:
            continue

        if details["location"] != current_location:
            travel_time = travel_times[(current_location, details["location"])]
            current_time += travel_time
            current_location = details["location"]

        if current_time >= details["end"]:
            continue

        meeting_start = max(current_time, details["start"])
        meeting_end = min(meeting_start + details["min_duration"], details["end"])

        if meeting_end > END_OF_DAY:
            continue

        new_itinerary = itinerary + [{
            "action": "meet",
            "location": details["location"],
            "person": friend,
            "start_time": time_to_str(meeting_start),
            "end_time": time_to_str(meeting_end)
        }]

        next_itinerary, next_end_time = find_best_schedule(
            current_location, meeting_end, visited_friends | {friend}, new_itinerary
        )

        if next_end_time < best_end_time:
            best_itinerary = next_itinerary
            best_end_time = next_end_time

        current_time = meeting_start  # Reset time after checking this path

    return best_itinerary, best_end_time

best_itinerary, _ = find_best_schedule("Embarcadero", START_TIME, set(), [])
result = {"itinerary": best_itinerary}

print(json.dumps(result, indent=2))