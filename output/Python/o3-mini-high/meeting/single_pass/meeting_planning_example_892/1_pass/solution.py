#!/usr/bin/env python3
import json
import copy

# Convert minutes (since midnight) to a "H:MM" 24-hour format string.
def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times (in minutes) between locations.
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
# Times are represented in minutes since midnight.
# For example, 9:00 AM is 540.
# Data: person, location, available start time, available end time, minimum meeting duration.
friends = [
    {"person": "Charles", "location": "Bayview", "avail_start": 11 * 60 + 30, "avail_end": 14 * 60 + 30, "min_duration": 45},
    {"person": "Robert", "location": "Sunset District", "avail_start": 16 * 60 + 45, "avail_end": 21 * 60 + 0, "min_duration": 30},
    {"person": "Karen", "location": "Richmond District", "avail_start": 19 * 60 + 15, "avail_end": 21 * 60 + 30, "min_duration": 60},
    {"person": "Rebecca", "location": "Nob Hill", "avail_start": 16 * 60 + 15, "avail_end": 20 * 60 + 30, "min_duration": 90},
    {"person": "Margaret", "location": "Chinatown", "avail_start": 14 * 60 + 15, "avail_end": 19 * 60 + 45, "min_duration": 120},
    {"person": "Patricia", "location": "Haight-Ashbury", "avail_start": 14 * 60 + 30, "avail_end": 20 * 60 + 30, "min_duration": 45},
    {"person": "Mark", "location": "North Beach", "avail_start": 14 * 60 + 0, "avail_end": 18 * 60 + 30, "min_duration": 105},
    {"person": "Melissa", "location": "Russian Hill", "avail_start": 13 * 60 + 0, "avail_end": 19 * 60 + 45, "min_duration": 30},
    {"person": "Laura", "location": "Embarcadero", "avail_start": 7 * 60 + 45, "avail_end": 13 * 60 + 15, "min_duration": 105}
]

# Global variables to store the best schedule found.
best_schedule = []
best_count = 0

# Depth-first search to try all orders of meetings.
def dfs(current_location, current_time, remaining, schedule):
    global best_schedule, best_count

    found_next = False

    for i, friend in enumerate(remaining):
        # Calculate travel time from the current location to the friend's location.
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # Meeting can only start when both you arrive and the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_duration"]
        # Check if the meeting can finish before the friend's end availability.
        if meeting_end <= friend["avail_end"]:
            found_next = True
            # Create the event entry.
            event = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["person"],
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            }
            new_schedule = schedule + [event]
            # Prepare a new list of remaining friends (remove the current friend).
            new_remaining = remaining[:i] + remaining[i+1:]
            # Recurse from the friend's location and meeting end time.
            dfs(friend["location"], meeting_end, new_remaining, new_schedule)
    # If no further meeting can be scheduled, update the best solution if this one has more meetings.
    if not found_next:
        if len(schedule) > best_count:
            best_count = len(schedule)
            best_schedule = schedule

def main():
    global best_schedule, best_count

    # Starting point: You arrive at Marina District at 9:00 AM (540 minutes).
    start_location = "Marina District"
    start_time = 9 * 60  # 540 minutes

    # Make a copy of the friends list.
    remaining_friends = friends[:]

    # Begin recursive search.
    dfs(start_location, start_time, remaining_friends, [])

    # Prepare the result in the required JSON format.
    result = {
        "itinerary": best_schedule
    }

    # Output the result as JSON.
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()