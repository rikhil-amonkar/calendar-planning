#!/usr/bin/env python3
import json

# Helper function: convert minutes since midnight to "H:MM" format (24-hour, no leading zero for hour)
def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times between locations (in minutes)
# Represented as a nested dictionary: travel_times[origin][destination] = time_in_minutes
travel_times = {
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Financial District": 5,
        "Russian Hill": 8,
        "Marina District": 12,
        "Richmond District": 21,
        "Pacific Heights": 11,
        "Haight-Ashbury": 21,
        "Presidio": 20,
        "Nob Hill": 10,
        "The Castro": 25,
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Financial District": 11,
        "Russian Hill": 7,
        "Marina District": 9,
        "Richmond District": 18,
        "Pacific Heights": 12,
        "Haight-Ashbury": 22,
        "Presidio": 17,
        "Nob Hill": 11,
        "The Castro": 27,
    },
    "Financial District": {
        "Embarcadero": 4,
        "Fisherman's Wharf": 10,
        "Russian Hill": 11,
        "Marina District": 15,
        "Richmond District": 21,
        "Pacific Heights": 13,
        "Haight-Ashbury": 19,
        "Presidio": 22,
        "Nob Hill": 8,
        "The Castro": 20,
    },
    "Russian Hill": {
        "Embarcadero": 8,
        "Fisherman's Wharf": 7,
        "Financial District": 11,
        "Marina District": 7,
        "Richmond District": 14,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Presidio": 14,
        "Nob Hill": 5,
        "The Castro": 21,
    },
    "Marina District": {
        "Embarcadero": 14,
        "Fisherman's Wharf": 10,
        "Financial District": 17,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Pacific Heights": 7,
        "Haight-Ashbury": 16,
        "Presidio": 10,
        "Nob Hill": 12,
        "The Castro": 22,
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Fisherman's Wharf": 18,
        "Financial District": 22,
        "Russian Hill": 13,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Presidio": 7,
        "Nob Hill": 17,
        "The Castro": 16,
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Fisherman's Wharf": 13,
        "Financial District": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "Richmond District": 12,
        "Haight-Ashbury": 11,
        "Presidio": 11,
        "Nob Hill": 8,
        "The Castro": 16,
    },
    "Haight-Ashbury": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Financial District": 21,
        "Russian Hill": 17,
        "Marina District": 17,
        "Richmond District": 10,
        "Pacific Heights": 12,
        "Presidio": 15,
        "Nob Hill": 15,
        "The Castro": 6,
    },
    "Presidio": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 19,
        "Financial District": 23,
        "Russian Hill": 14,
        "Marina District": 11,
        "Richmond District": 7,
        "Pacific Heights": 11,
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "The Castro": 21,
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Fisherman's Wharf": 10,
        "Financial District": 9,
        "Russian Hill": 5,
        "Marina District": 11,
        "Richmond District": 14,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Presidio": 17,
        "The Castro": 17,
    },
    "The Castro": {
        "Embarcadero": 22,
        "Fisherman's Wharf": 24,
        "Financial District": 21,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Presidio": 20,
        "Nob Hill": 16,
    },
}

# Meeting constraints for each friend.
# Times are expressed as minutes since midnight.
# Example: 9:00 AM -> 9*60 = 540, 15:30 -> 15*60+30 = 930, etc.
friends = [
    {
        "name": "Stephanie",
        "location": "Fisherman's Wharf",
        "start": 15 * 60 + 30,  # 15:30 -> 930
        "end": 22 * 60,         # 22:00 -> 1320
        "min": 30
    },
    {
        "name": "Lisa",
        "location": "Financial District",
        "start": 10 * 60 + 45,  # 10:45 -> 645
        "end": 17 * 60 + 15,    # 17:15 -> 1035
        "min": 15
    },
    {
        "name": "Melissa",
        "location": "Russian Hill",
        "start": 17 * 60,       # 17:00 -> 1020
        "end": 21 * 60 + 45,    # 21:45 -> 1305
        "min": 120
    },
    {
        "name": "Betty",
        "location": "Marina District",
        "start": 10 * 60 + 45,  # 10:45 -> 645
        "end": 14 * 60 + 15,    # 14:15 -> 855
        "min": 60
    },
    {
        "name": "Sarah",
        "location": "Richmond District",
        "start": 16 * 60 + 15,  # 16:15 -> 975
        "end": 19 * 60 + 30,    # 19:30 -> 1170
        "min": 105
    },
    {
        "name": "Daniel",
        "location": "Pacific Heights",
        "start": 18 * 60 + 30,  # 18:30 -> 1110
        "end": 21 * 60 + 45,    # 21:45 -> 1305
        "min": 60
    },
    {
        "name": "Joshua",
        "location": "Haight-Ashbury",
        "start": 9 * 60,        # 9:00 -> 540
        "end": 15 * 60 + 30,    # 15:30 -> 930
        "min": 15
    },
    {
        "name": "Joseph",
        "location": "Presidio",
        "start": 7 * 60,        # 7:00 -> 420
        "end": 13 * 60,         # 13:00 -> 780
        "min": 45
    },
    {
        "name": "Andrew",
        "location": "Nob Hill",
        "start": 19 * 60 + 45,  # 19:45 -> 1185
        "end": 22 * 60,         # 22:00 -> 1320
        "min": 105
    },
    {
        "name": "John",
        "location": "The Castro",
        "start": 13 * 60 + 15,  # 13:15 -> 795
        "end": 19 * 60 + 45,    # 19:45 -> 1185
        "min": 45
    }
]

# Global variable to store the best itinerary (the one with maximum meetings)
best_itinerary = []

# Depth-first search function to explore all possible meeting orders subject to time constraints.
def dfs(current_time, current_location, itinerary, remaining_friends):
    global best_itinerary

    # Update the best itinerary if this one has more meetings.
    if len(itinerary) > len(best_itinerary):
        best_itinerary = itinerary

    # Pruning: if even scheduling all remaining friends wouldn't beat best, then return.
    if len(itinerary) + len(remaining_friends) <= len(best_itinerary):
        return

    # Try scheduling each remaining friend next.
    for i, friend in enumerate(remaining_friends):
        # Get travel time from current location to friend's location.
        # If there's no explicit route, skip (should not happen with complete data).
        travel = travel_times[current_location].get(friend["location"], None)
        if travel is None:
            continue

        arrival_time = current_time + travel
        # The meeting cannot start before both our arrival and the friend's available start.
        meeting_start = max(arrival_time, friend["start"])
        meeting_end = meeting_start + friend["min"]

        # Check if the meeting can finish before the friend's availability ends.
        if meeting_end <= friend["end"]:
            # Create an event for this meeting.
            event = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            }
            new_itinerary = itinerary + [event]
            # Prepare new list of remaining friends without the current one.
            new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
            dfs(meeting_end, friend["location"], new_itinerary, new_remaining)

if __name__ == '__main__':
    # Start at Embarcadero at 9:00 AM (540 minutes).
    start_time = 9 * 60  # 540 minutes
    start_location = "Embarcadero"
    dfs(start_time, start_location, [], friends)

    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))