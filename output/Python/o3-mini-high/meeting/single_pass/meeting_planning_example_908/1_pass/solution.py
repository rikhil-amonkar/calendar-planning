#!/usr/bin/env python3
import json
import sys
import copy

# Helper function to convert time in minutes to "H:MM" 24-hour format (no leading zero needed for hour)
def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (in minutes) as provided.
# The keys are the origin locations and the values are dictionaries mapping destination to travel minutes.
travel_times = {
    "Financial District": {
        "Fisherman's Wharf": 10,
        "Presidio": 22,
        "Bayview": 19,
        "Haight-Ashbury": 19,
        "Russian Hill": 11,
        "The Castro": 20,
        "Marina District": 15,
        "Richmond District": 21,
        "Union Square": 9,
        "Sunset District": 30
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Presidio": 17,
        "Bayview": 26,
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
        "The Castro": 27,
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 13,
        "Sunset District": 27
    },
    "Presidio": {
        "Financial District": 23,
        "Fisherman's Wharf": 19,
        "Bayview": 31,
        "Haight-Ashbury": 15,
        "Russian Hill": 14,
        "The Castro": 21,
        "Marina District": 11,
        "Richmond District": 7,
        "Union Square": 22,
        "Sunset District": 15
    },
    "Bayview": {
        "Financial District": 19,
        "Fisherman's Wharf": 25,
        "Presidio": 32,
        "Haight-Ashbury": 19,
        "Russian Hill": 23,
        "The Castro": 19,
        "Marina District": 27,
        "Richmond District": 25,
        "Union Square": 18,
        "Sunset District": 23
    },
    "Haight-Ashbury": {
        "Financial District": 21,
        "Fisherman's Wharf": 23,
        "Presidio": 15,
        "Bayview": 18,
        "Russian Hill": 17,
        "The Castro": 6,
        "Marina District": 17,
        "Richmond District": 10,
        "Union Square": 19,
        "Sunset District": 15
    },
    "Russian Hill": {
        "Financial District": 11,
        "Fisherman's Wharf": 7,
        "Presidio": 14,
        "Bayview": 23,
        "Haight-Ashbury": 17,
        "The Castro": 21,
        "Marina District": 7,
        "Richmond District": 14,
        "Union Square": 10,
        "Sunset District": 23
    },
    "The Castro": {
        "Financial District": 21,
        "Fisherman's Wharf": 24,
        "Presidio": 20,
        "Bayview": 19,
        "Haight-Ashbury": 6,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Union Square": 19,
        "Sunset District": 17
    },
    "Marina District": {
        "Financial District": 17,
        "Fisherman's Wharf": 10,
        "Presidio": 10,
        "Bayview": 27,
        "Haight-Ashbury": 16,
        "Russian Hill": 8,
        "The Castro": 22,
        "Richmond District": 11,
        "Union Square": 16,
        "Sunset District": 19
    },
    "Richmond District": {
        "Financial District": 22,
        "Fisherman's Wharf": 18,
        "Presidio": 7,
        "Bayview": 27,
        "Haight-Ashbury": 10,
        "Russian Hill": 13,
        "The Castro": 16,
        "Marina District": 9,
        "Union Square": 21,
        "Sunset District": 11
    },
    "Union Square": {
        "Financial District": 9,
        "Fisherman's Wharf": 15,
        "Presidio": 24,
        "Bayview": 15,
        "Haight-Ashbury": 18,
        "Russian Hill": 13,
        "The Castro": 17,
        "Marina District": 18,
        "Richmond District": 20,
        "Sunset District": 27
    },
    "Sunset District": {
        "Financial District": 30,
        "Fisherman's Wharf": 29,
        "Presidio": 16,
        "Bayview": 22,
        "Haight-Ashbury": 15,
        "Russian Hill": 24,
        "The Castro": 17,
        "Marina District": 21,
        "Richmond District": 12,
        "Union Square": 30
    }
}

# Define meeting constraints for each friend.
# Times are stored in minutes since midnight.
# Financial District arrival is fixed at 9:00 (540 minutes)
friends = [
    { "name": "Mark", "location": "Fisherman's Wharf", "window_start": 495, "window_end": 600, "duration": 30 },
    { "name": "Ashley", "location": "Richmond District", "window_start": 585, "window_end": 675, "duration": 45 },
    { "name": "Brian", "location": "The Castro", "window_start": 555, "window_end": 795, "duration": 30 },
    { "name": "Joseph", "location": "Marina District", "window_start": 645, "window_end": 900, "duration": 90 },
    { "name": "Stephanie", "location": "Presidio", "window_start": 735, "window_end": 900, "duration": 75 },
    { "name": "Lisa", "location": "Haight-Ashbury", "window_start": 930, "window_end": 1110, "duration": 45 },
    { "name": "Patricia", "location": "Union Square", "window_start": 990, "window_end": 1200, "duration": 120 },
    { "name": "William", "location": "Russian Hill", "window_start": 1125, "window_end": 1200, "duration": 60 },
    { "name": "Karen", "location": "Sunset District", "window_start": 990, "window_end": 1320, "duration": 105 },
    { "name": "Betty", "location": "Bayview", "window_start": 435, "window_end": 1230, "duration": 15 }
]

# To maximize the number of friends met in the day,
# we will use a recursive backtracking search that
# attempts to schedule meetings (respecting travel times and time window constraints)
# starting from the Financial District at 9:00 (540 minutes).

best_count = 0
best_itinerary = []  # Will hold a list of tuples: (friend, meeting_start, meeting_end)

def search(curr_time, curr_loc, remaining, itinerary):
    global best_count, best_itinerary
    # Try scheduling each remaining friend next
    for i, friend in enumerate(remaining):
        # Check if travel time exists from current location to friend's location
        if curr_loc not in travel_times or friend["location"] not in travel_times[curr_loc]:
            continue
        travel = travel_times[curr_loc][friend["location"]]
        arrival = curr_time + travel
        # The meeting can only start when friend is available
        meeting_start = max(arrival, friend["window_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting can be completed within the friend's available window
        if meeting_end <= friend["window_end"]:
            new_itinerary = itinerary + [(friend, meeting_start, meeting_end)]
            new_remaining = remaining[:i] + remaining[i+1:]
            search(meeting_end, friend["location"], new_remaining, new_itinerary)
    # Update best solution if this itinerary is longer than the best found so far.
    if len(itinerary) > best_count:
        best_count = len(itinerary)
        best_itinerary = itinerary

def main():
    global best_count, best_itinerary
    start_time = 540  # 9:00 AM in minutes
    start_location = "Financial District"
    # We use a copy of friends as the initial remaining list.
    search(start_time, start_location, friends, [])
    
    # Prepare output in the required JSON format.
    # Each entry in the itinerary dictionary contains:
    # "action": "meet", "location": location, "person": friend name, "start_time": "H:MM", "end_time": "H:MM"
    output = {"itinerary": []}
    for entry in best_itinerary:
        friend, start, end = entry
        output["itinerary"].append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": format_time(start),
            "end_time": format_time(end)
        })
    # Output JSON-formatted dictionary.
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()