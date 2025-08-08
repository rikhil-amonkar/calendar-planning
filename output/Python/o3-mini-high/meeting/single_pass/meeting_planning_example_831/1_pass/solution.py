#!/usr/bin/env python3
import json
import sys

# Convert time in minutes since midnight to "H:MM" 24-hour format.
def minutes_to_time(m):
    h = m // 60
    minutes = m % 60
    return f"{h}:{minutes:02d}"

# Travel times between locations as provided.
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

# Define friend meeting constraints.
# Times are in minutes since midnight.
# 9:00 = 540, 7:45 = 465, 10:15 = 615, 10:45 = 645, 9:30 = 570, 9:45 = 585, etc.
friends = [
    {"name": "Jeffrey", "location": "Fisherman's Wharf", "avail_start": 615, "avail_end": 780, "duration": 90},
    {"name": "Ronald", "location": "Alamo Square", "avail_start": 465, "avail_end": 885, "duration": 120},
    {"name": "Jason", "location": "Financial District", "avail_start": 645, "avail_end": 960, "duration": 105},
    {"name": "Melissa", "location": "Union Square", "avail_start": 1065, "avail_end": 1095, "duration": 15},
    {"name": "Elizabeth", "location": "Sunset District", "avail_start": 885, "avail_end": 1050, "duration": 105},
    {"name": "Margaret", "location": "Embarcadero", "avail_start": 795, "avail_end": 1140, "duration": 90},
    {"name": "George", "location": "Golden Gate Park", "avail_start": 1140, "avail_end": 1320, "duration": 75},
    {"name": "Richard", "location": "Chinatown", "avail_start": 570, "avail_end": 1260, "duration": 15},
    {"name": "Laura", "location": "Richmond District", "avail_start": 585, "avail_end": 1080, "duration": 60}
]

# Global variables to hold the best itinerary (maximum number of friends met)
best_schedule = []
best_count = 0
best_finish_time = float('inf')

# Recursive backtracking search.
# current_loc: current location (string)
# current_time: current time (in minutes)
# remaining: list of remaining friend dictionaries
# itinerary: list of tuples (friend, meeting_start, meeting_end)
def search(current_loc, current_time, remaining, itinerary):
    global best_schedule, best_count, best_finish_time

    # Update best itinerary if current one beats the best (by count, then finish time)
    if len(itinerary) > best_count or (len(itinerary) == best_count and current_time < best_finish_time):
        best_count = len(itinerary)
        best_finish_time = current_time
        best_schedule = itinerary

    # Try each remaining friend in turn.
    for i, friend in enumerate(remaining):
        # Compute travel time from current location to friend's location.
        if current_loc not in travel_times or friend["location"] not in travel_times[current_loc]:
            continue
        travel_time = travel_times[current_loc][friend["location"]]
        arrival = current_time + travel_time
        # The meeting can only start when the friend is available.
        meeting_start = max(arrival, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]

        # Check if meeting can be completed within friend's available time.
        if meeting_end <= friend["avail_end"]:
            new_itinerary = itinerary + [(friend, meeting_start, meeting_end)]
            # Remove this friend from the remaining list.
            new_remaining = remaining[:i] + remaining[i+1:]
            search(friend["location"], meeting_end, new_remaining, new_itinerary)

# Starting conditions:
# Arrive at Presidio at 9:00 (540 minutes)
start_location = "Presidio"
start_time = 540

# Run the search over all friends.
search(start_location, start_time, friends, [])

# For this problem, our objective is to maximize the number of friends met.
# (Depending on constraints the optimal itinerary may not include all 9 friends.)
# In our computed solution the search will pick the itinerary with maximum count.

# Build the JSON output with the required structure.
itinerary_output = []
for meeting in best_schedule:
    friend, meet_start, meet_end = meeting
    item = {
        "action": "meet",
        "location": friend["location"],
        "person": friend["name"],
        "start_time": minutes_to_time(meet_start),
        "end_time": minutes_to_time(meet_end)
    }
    itinerary_output.append(item)

result = {"itinerary": itinerary_output}
print(json.dumps(result, indent=2))
sys.exit(0)