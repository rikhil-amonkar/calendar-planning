#!/usr/bin/env python3
import json
import copy

# Helper functions to convert between time strings ("H:MM") and minutes from midnight.
def time_to_minutes(t):
    # Assumes t is like "9:00" or "13:30"
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times dictionary as given.
travel_times = {
    "Nob Hill": {
        "Embarcadero": 9, "The Castro": 17, "Haight-Ashbury": 13, "Union Square": 7,
        "North Beach": 8, "Pacific Heights": 8, "Chinatown": 6, "Golden Gate Park": 17,
        "Marina District": 11, "Russian Hill": 5
    },
    "Embarcadero": {
        "Nob Hill": 10, "The Castro": 25, "Haight-Ashbury": 21, "Union Square": 10,
        "North Beach": 5, "Pacific Heights": 11, "Chinatown": 7, "Golden Gate Park": 25,
        "Marina District": 12, "Russian Hill": 8
    },
    "The Castro": {
        "Nob Hill": 16, "Embarcadero": 22, "Haight-Ashbury": 6, "Union Square": 17,
        "North Beach": 20, "Pacific Heights": 16, "Chinatown": 22, "Golden Gate Park": 11,
        "Marina District": 21, "Russian Hill": 18
    },
    "Haight-Ashbury": {
        "Nob Hill": 15, "Embarcadero": 20, "The Castro": 6, "Union Square": 19,
        "North Beach": 19, "Pacific Heights": 12, "Chinatown": 19, "Golden Gate Park": 7,
        "Marina District": 17, "Russian Hill": 17
    },
    "Union Square": {
        "Nob Hill": 9, "Embarcadero": 11, "The Castro": 17, "Haight-Ashbury": 18,
        "North Beach": 10, "Pacific Heights": 15, "Chinatown": 7, "Golden Gate Park": 22,
        "Marina District": 18, "Russian Hill": 13
    },
    "North Beach": {
        "Nob Hill": 7, "Embarcadero": 6, "The Castro": 23, "Haight-Ashbury": 18,
        "Union Square": 7, "Pacific Heights": 8, "Chinatown": 6, "Golden Gate Park": 22,
        "Marina District": 9, "Russian Hill": 4
    },
    "Pacific Heights": {
        "Nob Hill": 8, "Embarcadero": 10, "The Castro": 16, "Haight-Ashbury": 11,
        "Union Square": 12, "North Beach": 9, "Chinatown": 11, "Golden Gate Park": 15,
        "Marina District": 6, "Russian Hill": 7
    },
    "Chinatown": {
        "Nob Hill": 9, "Embarcadero": 5, "The Castro": 22, "Haight-Ashbury": 19,
        "Union Square": 7, "North Beach": 3, "Pacific Heights": 10, "Golden Gate Park": 23,
        "Marina District": 12, "Russian Hill": 7
    },
    "Golden Gate Park": {
        "Nob Hill": 20, "Embarcadero": 25, "The Castro": 13, "Haight-Ashbury": 7,
        "Union Square": 22, "North Beach": 23, "Pacific Heights": 16, "Chinatown": 23,
        "Marina District": 16, "Russian Hill": 19
    },
    "Marina District": {
        "Nob Hill": 12, "Embarcadero": 14, "The Castro": 22, "Haight-Ashbury": 16,
        "Union Square": 16, "North Beach": 11, "Pacific Heights": 7, "Chinatown": 15,
        "Golden Gate Park": 18, "Russian Hill": 8
    },
    "Russian Hill": {
        "Nob Hill": 5, "Embarcadero": 8, "The Castro": 21, "Haight-Ashbury": 17,
        "Union Square": 10, "North Beach": 5, "Pacific Heights": 7, "Chinatown": 9,
        "Golden Gate Park": 21, "Marina District": 7
    }
}

# Friends meeting constraints data.
# For each friend, we store: name, location, available start time, available end time, minimum meeting duration (in minutes)
friends = [
    {"name": "Mary", "location": "Embarcadero", "avail_start": time_to_minutes("20:00"), "avail_end": time_to_minutes("21:15"), "duration": 75},
    {"name": "Kenneth", "location": "The Castro", "avail_start": time_to_minutes("11:15"), "avail_end": time_to_minutes("19:15"), "duration": 30},
    {"name": "Joseph", "location": "Haight-Ashbury", "avail_start": time_to_minutes("20:00"), "avail_end": time_to_minutes("22:00"), "duration": 120},
    {"name": "Sarah", "location": "Union Square", "avail_start": time_to_minutes("11:45"), "avail_end": time_to_minutes("14:30"), "duration": 90},
    {"name": "Thomas", "location": "North Beach", "avail_start": time_to_minutes("19:15"), "avail_end": time_to_minutes("19:45"), "duration": 15},
    {"name": "Daniel", "location": "Pacific Heights", "avail_start": time_to_minutes("13:45"), "avail_end": time_to_minutes("20:30"), "duration": 15},
    {"name": "Richard", "location": "Chinatown", "avail_start": time_to_minutes("8:00"), "avail_end": time_to_minutes("18:45"), "duration": 30},
    {"name": "Mark", "location": "Golden Gate Park", "avail_start": time_to_minutes("17:30"), "avail_end": time_to_minutes("21:30"), "duration": 120},
    {"name": "David", "location": "Marina District", "avail_start": time_to_minutes("20:00"), "avail_end": time_to_minutes("21:00"), "duration": 60},
    {"name": "Karen", "location": "Russian Hill", "avail_start": time_to_minutes("13:15"), "avail_end": time_to_minutes("18:30"), "duration": 120}
]

# Global best itinerary to maximize number of meetings.
best_itinerary = []

# DFS/backtracking to try all meeting orders that satisfy travel and availability constraints.
def dfs(current_time, current_loc, remaining, current_schedule):
    global best_itinerary
    # Update best itinerary if current schedule has more meetings than best so far.
    if len(current_schedule) > len(best_itinerary):
        best_itinerary = copy.deepcopy(current_schedule)
    
    # Try each remaining friend.
    for i, friend in enumerate(remaining):
        # Compute travel time from current_loc to friend's location.
        if current_loc == friend["location"]:
            travel = 0
        else:
            travel = travel_times[current_loc][friend["location"]]
        arrival_time = current_time + travel
        # The meeting can only start at the later of arrival or friend's available start.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting can be completed before friend's available end time.
        if meeting_end <= friend["avail_end"]:
            # Accept this meeting.
            meeting = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            # Prepare new list of remaining friends.
            new_remaining = remaining[:i] + remaining[i+1:]
            # Continue DFS from friend's location, with time updated to meeting_end.
            dfs(meeting_end, friend["location"], new_remaining, current_schedule + [meeting])
    # Also allow finish here (i.e. do not schedule further meetings).

def main():
    # Starting point: Nob Hill at 9:00.
    start_time = time_to_minutes("9:00")
    start_location = "Nob Hill"
    
    # Create a copy of friends list.
    remaining_friends = friends[:]
    
    # Run DFS to compute optimal itinerary.
    dfs(start_time, start_location, remaining_friends, [])
    
    # Prepare output dictionary in required JSON format.
    output = {"itinerary": best_itinerary}
    print(json.dumps(output, indent=2))
    
if __name__ == "__main__":
    main()