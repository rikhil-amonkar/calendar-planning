#!/usr/bin/env python3
import json

# Helper function to convert minutes since midnight to HH:MM (24‐hour format without a leading zero for hour)
def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define the travel times (in minutes) as provided.
travel_times = {
    "Presidio": {
        "Fisherman's Wharf": 19,
        "Alamo Square": 19,
        "Financial District": 23,
        "Union Square": 22,
        "Sunset District": 15,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Alamo Square": 21,
        "Financial District": 11,
        "Union Square": 13,
        "Sunset District": 27,
        "Embarcadero": 8,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Richmond District": 18
    },
    "Alamo Square": {
        "Presidio": 17,
        "Fisherman's Wharf": 19,
        "Financial District": 17,
        "Union Square": 14,
        "Sunset District": 16,
        "Embarcadero": 16,
        "Golden Gate Park": 9,
        "Chinatown": 15,
        "Richmond District": 11
    },
    "Financial District": {
        "Presidio": 22,
        "Fisherman's Wharf": 10,
        "Alamo Square": 17,
        "Union Square": 9,
        "Sunset District": 30,
        "Embarcadero": 4,
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Richmond District": 21
    },
    "Union Square": {
        "Presidio": 24,
        "Fisherman's Wharf": 15,
        "Alamo Square": 15,
        "Financial District": 9,
        "Sunset District": 27,
        "Embarcadero": 11,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Richmond District": 20
    },
    "Sunset District": {
        "Presidio": 16,
        "Fisherman's Wharf": 29,
        "Alamo Square": 17,
        "Financial District": 30,
        "Union Square": 30,
        "Embarcadero": 30,
        "Golden Gate Park": 11,
        "Chinatown": 30,
        "Richmond District": 12
    },
    "Embarcadero": {
        "Presidio": 20,
        "Fisherman's Wharf": 6,
        "Alamo Square": 19,
        "Financial District": 5,
        "Union Square": 10,
        "Sunset District": 30,
        "Golden Gate Park": 25,
        "Chinatown": 7,
        "Richmond District": 21
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Fisherman's Wharf": 24,
        "Alamo Square": 9,
        "Financial District": 26,
        "Union Square": 22,
        "Sunset District": 10,
        "Embarcadero": 25,
        "Chinatown": 23,
        "Richmond District": 7
    },
    "Chinatown": {
        "Presidio": 19,
        "Fisherman's Wharf": 8,
        "Alamo Square": 17,
        "Financial District": 5,
        "Union Square": 7,
        "Sunset District": 29,
        "Embarcadero": 5,
        "Golden Gate Park": 23,
        "Richmond District": 20
    },
    "Richmond District": {
        "Presidio": 7,
        "Fisherman's Wharf": 18,
        "Alamo Square": 13,
        "Financial District": 22,
        "Union Square": 21,
        "Sunset District": 11,
        "Embarcadero": 19,
        "Golden Gate Park": 9,
        "Chinatown": 20
    }
}

# Define the meeting constraints for each friend.
# Times are represented as minutes since midnight.
friends = [
    {
        "name": "Jeffrey",
        "location": "Fisherman's Wharf",
        "avail_start": 10 * 60 + 15,  # 10:15 -> 615
        "avail_end": 13 * 60 + 0,     # 13:00 -> 780
        "min_duration": 90
    },
    {
        "name": "Ronald",
        "location": "Alamo Square",
        "avail_start": 7 * 60 + 45,   # 7:45 -> 465
        "avail_end": 14 * 60 + 45,    # 14:45 -> 885
        "min_duration": 120
    },
    {
        "name": "Jason",
        "location": "Financial District",
        "avail_start": 10 * 60 + 45,  # 10:45 -> 645
        "avail_end": 16 * 60 + 0,     # 16:00 -> 960
        "min_duration": 105
    },
    {
        "name": "Melissa",
        "location": "Union Square",
        "avail_start": 17 * 60 + 45,  # 17:45 -> 1065
        "avail_end": 18 * 60 + 15,    # 18:15 -> 1095
        "min_duration": 15
    },
    {
        "name": "Elizabeth",
        "location": "Sunset District",
        "avail_start": 14 * 60 + 45,  # 14:45 -> 885
        "avail_end": 17 * 60 + 30,    # 17:30 -> 1050
        "min_duration": 105
    },
    {
        "name": "Margaret",
        "location": "Embarcadero",
        "avail_start": 13 * 60 + 15,  # 13:15 -> 795
        "avail_end": 19 * 60 + 0,     # 19:00 -> 1140
        "min_duration": 90
    },
    {
        "name": "George",
        "location": "Golden Gate Park",
        "avail_start": 19 * 60 + 0,   # 19:00 -> 1140
        "avail_end": 22 * 60 + 0,     # 22:00 -> 1320
        "min_duration": 75
    },
    {
        "name": "Richard",
        "location": "Chinatown",
        "avail_start": 9 * 60 + 30,   # 9:30 -> 570
        "avail_end": 21 * 60 + 0,     # 21:00 -> 1260
        "min_duration": 15
    },
    {
        "name": "Laura",
        "location": "Richmond District",
        "avail_start": 9 * 60 + 45,   # 9:45 -> 585
        "avail_end": 18 * 60 + 0,     # 18:00 -> 1080
        "min_duration": 60
    }
]

# We want to compute an itinerary that “meets as many friends as possible”
# We use a recursive backtracking search that, given a current location, current time, and
# a list of unscheduled friends, will try to schedule a meeting if possible.
def search(curr_loc, curr_time, remaining):
    best_count = 0
    best_itinerary = []
    # Try each friend in the remaining list
    for i, friend in enumerate(remaining):
        # Determine travel time from current location to friend's location.
        if curr_loc in travel_times and friend["location"] in travel_times[curr_loc]:
            travel = travel_times[curr_loc][friend["location"]]
        else:
            continue
        arrival_time = curr_time + travel
        # We can only start the meeting when the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_duration"]
        # Check if the meeting (of minimum duration) can be done before the friend leaves.
        if meeting_end <= friend["avail_end"]:
            # Create a meeting step.
            step = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            # Recurse with updated state.
            next_remaining = remaining[:i] + remaining[i+1:]
            count, itinerary = search(friend["location"], meeting_end, next_remaining)
            count += 1  # Count this meeting.
            itinerary = [step] + itinerary
            if count > best_count:
                best_count = count
                best_itinerary = itinerary
    return best_count, best_itinerary

# Starting conditions:
# You arrive at Presidio at 9:00 (9*60 = 540 minutes).
start_location = "Presidio"
start_time = 9 * 60  # 9:00 AM -> 540 minutes

# Compute the optimal itinerary (maximizing the number of meetings).
max_count, best_itin = search(start_location, start_time, friends)

# The result is output as a JSON-formatted dictionary.
result = {"itinerary": best_itin}
print(json.dumps(result, indent=2))