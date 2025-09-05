import json

def format_time(minutes):
    hr = minutes // 60
    mn = minutes % 60
    return f"{hr}:{mn:02d}"

# Travel times in minutes between locations.
travel_times = {
    "Marina District": {
        "Bayview": 27,
        "Sunset District": 19,
        "Richmond District": 11,
        "Nob Hill": 12,
        "Chinatown": 15,
        "Haight-Ashbury": 16,
        "North Beach": 11,
        "Russian Hill": 8,
        "Embarcadero": 14
    },
    "Bayview": {
        "Marina District": 27,
        "Sunset District": 23,
        "Richmond District": 25,
        "Nob Hill": 20,
        "Chinatown": 19,
        "Haight-Ashbury": 19,
        "North Beach": 22,
        "Russian Hill": 23,
        "Embarcadero": 19
    },
    "Sunset District": {
        "Marina District": 21,
        "Bayview": 22,
        "Richmond District": 12,
        "Nob Hill": 27,
        "Chinatown": 30,
        "Haight-Ashbury": 15,
        "North Beach": 28,
        "Russian Hill": 24,
        "Embarcadero": 30
    },
    "Richmond District": {
        "Marina District": 9,
        "Bayview": 27,
        "Sunset District": 11,
        "Nob Hill": 17,
        "Chinatown": 20,
        "Haight-Ashbury": 10,
        "North Beach": 17,
        "Russian Hill": 13,
        "Embarcadero": 19
    },
    "Nob Hill": {
        "Marina District": 11,
        "Bayview": 19,
        "Sunset District": 24,
        "Richmond District": 14,
        "Chinatown": 6,
        "Haight-Ashbury": 13,
        "North Beach": 8,
        "Russian Hill": 5,
        "Embarcadero": 9
    },
    "Chinatown": {
        "Marina District": 12,
        "Bayview": 20,
        "Sunset District": 29,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Haight-Ashbury": 19,
        "North Beach": 3,
        "Russian Hill": 7,
        "Embarcadero": 5
    },
    "Haight-Ashbury": {
        "Marina District": 17,
        "Bayview": 18,
        "Sunset District": 15,
        "Richmond District": 10,
        "Nob Hill": 15,
        "Chinatown": 19,
        "North Beach": 19,
        "Russian Hill": 17,
        "Embarcadero": 20
    },
    "North Beach": {
        "Marina District": 9,
        "Bayview": 25,
        "Sunset District": 27,
        "Richmond District": 18,
        "Nob Hill": 7,
        "Chinatown": 6,
        "Haight-Ashbury": 18,
        "Russian Hill": 4,
        "Embarcadero": 6
    },
    "Russian Hill": {
        "Marina District": 7,
        "Bayview": 23,
        "Sunset District": 23,
        "Richmond District": 14,
        "Nob Hill": 5,
        "Chinatown": 9,
        "Haight-Ashbury": 17,
        "North Beach": 5,
        "Embarcadero": 8
    },
    "Embarcadero": {
        "Marina District": 12,
        "Bayview": 21,
        "Sunset District": 30,
        "Richmond District": 21,
        "Nob Hill": 10,
        "Chinatown": 7,
        "Haight-Ashbury": 21,
        "North Beach": 5,
        "Russian Hill": 8
    }
}

# Meeting constraints for each friend.
# Times are stored as minutes since midnight.
meetings = [
    {"person": "Laura", "location": "Embarcadero", "avail_start": 7 * 60 + 45, "avail_end": 13 * 60 + 15, "duration": 105},
    {"person": "Charles", "location": "Bayview", "avail_start": 11 * 60 + 30, "avail_end": 14 * 60 + 30, "duration": 45},
    {"person": "Melissa", "location": "Russian Hill", "avail_start": 13 * 60 + 0, "avail_end": 19 * 60 + 45, "duration": 30},
    {"person": "Margaret", "location": "Chinatown", "avail_start": 14 * 60 + 15, "avail_end": 19 * 60 + 45, "duration": 120},
    {"person": "Patricia", "location": "Haight-Ashbury", "avail_start": 14 * 60 + 30, "avail_end": 20 * 60 + 30, "duration": 45},
    {"person": "Mark", "location": "North Beach", "avail_start": 14 * 60 + 0, "avail_end": 18 * 60 + 30, "duration": 105},
    {"person": "Rebecca", "location": "Nob Hill", "avail_start": 16 * 60 + 15, "avail_end": 20 * 60 + 30, "duration": 90},
    {"person": "Robert", "location": "Sunset District", "avail_start": 16 * 60 + 45, "avail_end": 21 * 60 + 0, "duration": 30},
    {"person": "Karen", "location": "Richmond District", "avail_start": 19 * 60 + 15, "avail_end": 21 * 60 + 30, "duration": 60}
]

# Global variables to keep track of the best schedule (maximizing number of friends met).
best_count = 0
best_schedule = []

def dfs(current_time, current_location, remaining, schedule):
    global best_count, best_schedule
    # Update the best schedule if this one has more meetings.
    if len(schedule) > best_count:
        best_count = len(schedule)
        best_schedule = schedule.copy()
    # Try scheduling each remaining meeting.
    for i, meeting in enumerate(remaining):
        # Compute travel time from current_location to the meeting's location.
        if current_location in travel_times and meeting["location"] in travel_times[current_location]:
            travel = travel_times[current_location][meeting["location"]]
        else:
            continue
        arrival_time = current_time + travel
        # The meeting can start no earlier than when you arrive and its available start time.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if the meeting can be completed before the friend’s availability ends.
        if meeting_end <= meeting["avail_end"]:
            meeting_event = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start": meeting_start,
                "end": meeting_end
            }
            new_schedule = schedule + [meeting_event]
            new_remaining = remaining[:i] + remaining[i+1:]
            dfs(meeting_end, meeting["location"], new_remaining, new_schedule)

if __name__ == "__main__":
    # You arrive at Marina District at 9:00 AM.
    start_time = 9 * 60  # 9:00 AM in minutes since midnight
    start_location = "Marina District"
    
    # Recursively search for the best meeting schedule.
    dfs(start_time, start_location, meetings, [])
    
    # Convert the computed best schedule to the required JSON output format.
    itinerary = []
    for event in best_schedule:
        itinerary.append({
            "action": event["action"],
            "location": event["location"],
            "person": event["person"],
            "start_time": format_time(event["start"]),
            "end_time": format_time(event["end"])
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))