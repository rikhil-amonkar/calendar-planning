import json

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times (in minutes) between locations
travel_times = {
    "Russian Hill": {
        "Pacific Heights": 7,
        "North Beach": 5,
        "Golden Gate Park": 21,
        "Embarcadero": 8,
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "Mission District": 16,
        "Alamo Square": 15,
        "Bayview": 23,
        "Richmond District": 14,
    },
    "Pacific Heights": {
        "Russian Hill": 7,
        "North Beach": 9,
        "Golden Gate Park": 15,
        "Embarcadero": 10,
        "Haight-Ashbury": 11,
        "Fisherman's Wharf": 13,
        "Mission District": 15,
        "Alamo Square": 10,
        "Bayview": 22,
        "Richmond District": 12,
    },
    "North Beach": {
        "Russian Hill": 4,
        "Pacific Heights": 8,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Fisherman's Wharf": 5,
        "Mission District": 18,
        "Alamo Square": 16,
        "Bayview": 25,
        "Richmond District": 18,
    },
    "Golden Gate Park": {
        "Russian Hill": 19,
        "Pacific Heights": 16,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "Mission District": 17,
        "Alamo Square": 9,
        "Bayview": 23,
        "Richmond District": 7,
    },
    "Embarcadero": {
        "Russian Hill": 8,
        "Pacific Heights": 11,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Fisherman's Wharf": 6,
        "Mission District": 20,
        "Alamo Square": 19,
        "Bayview": 21,
        "Richmond District": 21,
    },
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Pacific Heights": 12,
        "North Beach": 19,
        "Golden Gate Park": 7,
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Mission District": 11,
        "Alamo Square": 5,
        "Bayview": 18,
        "Richmond District": 10,
    },
    "Fisherman's Wharf": {
        "Russian Hill": 7,
        "Pacific Heights": 12,
        "North Beach": 6,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Alamo Square": 21,
        "Bayview": 26,
        "Richmond District": 18,
    },
    "Mission District": {
        "Russian Hill": 15,
        "Pacific Heights": 16,
        "North Beach": 17,
        "Golden Gate Park": 17,
        "Embarcadero": 19,
        "Haight-Ashbury": 12,
        "Fisherman's Wharf": 22,
        "Alamo Square": 11,
        "Bayview": 14,
        "Richmond District": 20,
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Pacific Heights": 10,
        "North Beach": 15,
        "Golden Gate Park": 9,
        "Embarcadero": 16,
        "Haight-Ashbury": 5,
        "Fisherman's Wharf": 19,
        "Mission District": 10,
        "Bayview": 16,
        "Richmond District": 11,
    },
    "Bayview": {
        "Russian Hill": 23,
        "Pacific Heights": 23,
        "North Beach": 22,
        "Golden Gate Park": 22,
        "Embarcadero": 19,
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 25,
        "Mission District": 13,
        "Alamo Square": 16,
        "Richmond District": 25,
    },
    "Richmond District": {
        "Russian Hill": 13,
        "Pacific Heights": 10,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Fisherman's Wharf": 18,
        "Mission District": 20,
        "Alamo Square": 13,
        "Bayview": 27,
    }
}

# Friend meeting constraints.
# Times are stored in minutes since midnight.
friends = [
    {
        "name": "Emily",
        "location": "Pacific Heights",
        "avail_start": 9 * 60 + 15,  # 9:15
        "avail_end": 13 * 60 + 45,   # 13:45
        "duration": 120
    },
    {
        "name": "Helen",
        "location": "North Beach",
        "avail_start": 13 * 60 + 45,  # 13:45
        "avail_end": 18 * 60 + 45,    # 18:45
        "duration": 30
    },
    {
        "name": "Kimberly",
        "location": "Golden Gate Park",
        "avail_start": 18 * 60 + 45,  # 18:45
        "avail_end": 21 * 60 + 15,    # 21:15
        "duration": 75
    },
    {
        "name": "James",
        "location": "Embarcadero",
        "avail_start": 10 * 60 + 30,  # 10:30
        "avail_end": 11 * 60 + 30,    # 11:30
        "duration": 30
    },
    {
        "name": "Linda",
        "location": "Haight-Ashbury",
        "avail_start": 7 * 60 + 30,   # 7:30
        "avail_end": 19 * 60 + 15,    # 19:15
        "duration": 15
    },
    {
        "name": "Paul",
        "location": "Fisherman's Wharf",
        "avail_start": 14 * 60 + 45,  # 14:45
        "avail_end": 18 * 60 + 45,    # 18:45
        "duration": 90
    },
    {
        "name": "Anthony",
        "location": "Mission District",
        "avail_start": 8 * 60,        # 8:00
        "avail_end": 14 * 60 + 45,     # 14:45
        "duration": 105
    },
    {
        "name": "Nancy",
        "location": "Alamo Square",
        "avail_start": 8 * 60 + 30,   # 8:30
        "avail_end": 13 * 60 + 45,    # 13:45
        "duration": 120
    },
    {
        "name": "William",
        "location": "Bayview",
        "avail_start": 17 * 60 + 30,  # 17:30
        "avail_end": 20 * 60 + 30,    # 20:30
        "duration": 120
    },
    {
        "name": "Margaret",
        "location": "Richmond District",
        "avail_start": 15 * 60 + 15,  # 15:15
        "avail_end": 18 * 60 + 15,    # 18:15
        "duration": 45
    }
]

# Globals to store the best (maximized count) itinerary found.
best_itinerary = []
best_count = 0

def dfs(current_location, current_time, visited, itinerary):
    global best_itinerary, best_count
    found_next = False
    for friend in friends:
        if friend["name"] in visited:
            continue
        # Calculate time to travel from current location to the friend's location.
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # The meeting can only start once the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        # Check if there is enough time to complete the meeting before their availability ends.
        if meeting_start + friend["duration"] <= friend["avail_end"]:
            meeting_end = meeting_start + friend["duration"]
            meeting = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            }
            new_itinerary = itinerary + [meeting]
            new_visited = visited.copy()
            new_visited.add(friend["name"])
            dfs(friend["location"], meeting_end, new_visited, new_itinerary)
            found_next = True
    # If no further meetings can be added, update the best itinerary if this branch has more meetings.
    if not found_next:
        if len(itinerary) > best_count:
            best_count = len(itinerary)
            best_itinerary = itinerary

def main():
    # Start at Russian Hill at 9:00 AM (540 minutes).
    start_location = "Russian Hill"
    start_time = 9 * 60
    dfs(start_location, start_time, set(), [])
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()