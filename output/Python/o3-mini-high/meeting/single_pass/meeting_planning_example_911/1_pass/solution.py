#!/usr/bin/env python3
import json

def time_to_minutes(t):
    # Converts a time string "H:MM" to minutes after midnight.
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    # Converts minutes after midnight to a time string "H:MM" (24-hour format, no leading zero for hour)
    h = m // 60
    min_val = m % 60
    return f"{h}:{min_val:02d}"

# Travel time matrix (in minutes)
travel_times = {
    "The Castro": {
        "North Beach": 20,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Richmond District": 16,
        "Nob Hill": 16,
        "Marina District": 21,
        "Presidio": 20,
        "Union Square": 19,
        "Financial District": 21
    },
    "North Beach": {
        "The Castro": 23,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Richmond District": 18,
        "Nob Hill": 7,
        "Marina District": 9,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 8
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Richmond District": 7,
        "Nob Hill": 20,
        "Marina District": 16,
        "Presidio": 11,
        "Union Square": 22,
        "Financial District": 26
    },
    "Embarcadero": {
        "The Castro": 25,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Haight-Ashbury": 20,
        "Richmond District": 21,
        "Nob Hill": 10,
        "Marina District": 12,
        "Presidio": 20,
        "Union Square": 10,
        "Financial District": 5
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "North Beach": 19,
        "Golden Gate Park": 7,
        "Embarcadero": 20,
        "Richmond District": 10,
        "Nob Hill": 15,
        "Marina District": 17,
        "Presidio": 15,
        "Union Square": 19,
        "Financial District": 21
    },
    "Richmond District": {
        "The Castro": 16,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Nob Hill": 17,
        "Marina District": 9,
        "Presidio": 7,
        "Union Square": 21,
        "Financial District": 22
    },
    "Nob Hill": {
        "The Castro": 17,
        "North Beach": 8,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Haight-Ashbury": 13,
        "Richmond District": 14,
        "Marina District": 11,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 9
    },
    "Marina District": {
        "The Castro": 22,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Haight-Ashbury": 16,
        "Richmond District": 11,
        "Nob Hill": 12,
        "Presidio": 10,
        "Union Square": 16,
        "Financial District": 17
    },
    "Presidio": {
        "The Castro": 21,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Haight-Ashbury": 15,
        "Richmond District": 7,
        "Nob Hill": 18,
        "Marina District": 11,
        "Union Square": 22,
        "Financial District": 23
    },
    "Union Square": {
        "The Castro": 17,
        "North Beach": 10,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Haight-Ashbury": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Marina District": 18,
        "Presidio": 24,
        "Financial District": 9
    },
    "Financial District": {
        "The Castro": 20,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "Haight-Ashbury": 19,
        "Richmond District": 21,
        "Nob Hill": 8,
        "Marina District": 15,
        "Presidio": 22,
        "Union Square": 9
    }
}

# Define friend meeting constraints.
# Each friend: person, location, available start, available end, and minimum meeting duration (in minutes).
friends = [
    {
        "person": "Steven",
        "location": "North Beach",
        "avail_start": time_to_minutes("17:30"),
        "avail_end": time_to_minutes("20:30"),
        "duration": 15
    },
    {
        "person": "Sarah",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("17:00"),
        "avail_end": time_to_minutes("19:15"),
        "duration": 75
    },
    {
        "person": "Brian",
        "location": "Embarcadero",
        "avail_start": time_to_minutes("14:15"),
        "avail_end": time_to_minutes("16:00"),
        "duration": 105
    },
    {
        "person": "Stephanie",
        "location": "Haight-Ashbury",
        "avail_start": time_to_minutes("10:15"),
        "avail_end": time_to_minutes("12:15"),
        "duration": 75
    },
    {
        "person": "Melissa",
        "location": "Richmond District",
        "avail_start": time_to_minutes("14:00"),
        "avail_end": time_to_minutes("19:30"),
        "duration": 30
    },
    {
        "person": "Nancy",
        "location": "Nob Hill",
        "avail_start": time_to_minutes("8:15"),
        "avail_end": time_to_minutes("12:45"),
        "duration": 90
    },
    {
        "person": "David",
        "location": "Marina District",
        "avail_start": time_to_minutes("11:15"),
        "avail_end": time_to_minutes("13:15"),
        "duration": 120
    },
    {
        "person": "James",
        "location": "Presidio",
        "avail_start": time_to_minutes("15:00"),
        "avail_end": time_to_minutes("18:15"),
        "duration": 120
    },
    {
        "person": "Elizabeth",
        "location": "Union Square",
        "avail_start": time_to_minutes("11:30"),
        "avail_end": time_to_minutes("21:00"),
        "duration": 60
    },
    {
        "person": "Robert",
        "location": "Financial District",
        "avail_start": time_to_minutes("13:15"),
        "avail_end": time_to_minutes("15:15"),
        "duration": 45
    }
]

# Global variables to track the best (maximum friend count) itinerary.
best_schedule = []
best_count = 0

def dfs(current_location, current_time, remaining_friends, current_schedule):
    global best_schedule, best_count
    found_next = False
    # Try scheduling each remaining friend.
    for i, friend in enumerate(remaining_friends):
        # Calculate travel time from current location to friend's location.
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        # Meeting can only start when both you and the friend are available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting can be completed within friend's available window.
        if meeting_end <= friend["avail_end"]:
            found_next = True
            schedule_item = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_schedule = current_schedule + [schedule_item]
            # Remove the scheduled friend from the remaining list.
            new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
            dfs(friend["location"], meeting_end, new_remaining, new_schedule)
    # If no further friend can be scheduled from here, update best schedule if current is better.
    if not found_next:
        if len(current_schedule) > best_count:
            best_count = len(current_schedule)
            best_schedule = current_schedule

def main():
    # Starting point: The Castro at 9:00AM (540 minutes after midnight)
    start_location = "The Castro"
    start_time = time_to_minutes("9:00")
    dfs(start_location, start_time, friends, [])
    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()