import json
import sys
from copy import deepcopy

# Helper function: Convert minutes (since midnight) into a time string "H:MM"
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Define travel times (in minutes) as provided.
# The keys are location names.
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
        "Richmond District": 11,
        "Union Square": 30
    }
}

# Define the meeting constraints.
# Times are converted to minutes since midnight.
# For example, 9:00 AM is 9 * 60 = 540.
friends = [
    {
        "person": "Mark",
        "location": "Fisherman's Wharf",
        "avail_start": 8 * 60 + 15,    # 8:15 = 495
        "avail_end": 10 * 60,          # 10:00 = 600
        "duration": 30
    },
    {
        "person": "Stephanie",
        "location": "Presidio",
        "avail_start": 12 * 60 + 15,   # 12:15 = 735
        "avail_end": 15 * 60,          # 15:00 = 900
        "duration": 75
    },
    {
        "person": "Betty",
        "location": "Bayview",
        "avail_start": 7 * 60 + 15,    # 7:15 = 435
        "avail_end": 20 * 60 + 30,     # 20:30 = 1230
        "duration": 15
    },
    {
        "person": "Lisa",
        "location": "Haight-Ashbury",
        "avail_start": 15 * 60 + 30,   # 15:30 = 930
        "avail_end": 18 * 60 + 30,     # 18:30 = 1110
        "duration": 45
    },
    {
        "person": "William",
        "location": "Russian Hill",
        "avail_start": 18 * 60 + 45,   # 18:45 = 1125
        "avail_end": 20 * 60,          # 20:00 = 1200
        "duration": 60
    },
    {
        "person": "Brian",
        "location": "The Castro",
        "avail_start": 9 * 60 + 15,    # 9:15 = 555
        "avail_end": 13 * 60 + 15,     # 13:15 = 795
        "duration": 30
    },
    {
        "person": "Joseph",
        "location": "Marina District",
        "avail_start": 10 * 60 + 45,   # 10:45 = 645
        "avail_end": 15 * 60,          # 15:00 = 900
        "duration": 90
    },
    {
        "person": "Ashley",
        "location": "Richmond District",
        "avail_start": 9 * 60 + 45,    # 9:45 = 585
        "avail_end": 11 * 60 + 15,     # 11:15 = 675
        "duration": 45
    },
    {
        "person": "Patricia",
        "location": "Union Square",
        "avail_start": 16 * 60 + 30,   # 16:30 = 990
        "avail_end": 20 * 60,          # 20:00 = 1200
        "duration": 120
    },
    {
        "person": "Karen",
        "location": "Sunset District",
        "avail_start": 16 * 60 + 30,   # 16:30 = 990
        "avail_end": 22 * 60,          # 22:00 = 1320
        "duration": 105
    }
]

# Global variables to store the best (maximum count) itinerary
best_itinerary = []
best_count = 0

# Recursive backtracking search to build a feasible meeting schedule.
def search(current_time, current_location, remaining, current_schedule):
    global best_itinerary, best_count
    
    # Update best schedule if current has more meetings
    if len(current_schedule) > best_count:
        best_count = len(current_schedule)
        best_itinerary = deepcopy(current_schedule)
        
    # Try to schedule each remaining meeting if possible.
    for i, friend in enumerate(remaining):
        # Get travel time from current_location to friend's location.
        if current_location not in travel_times or friend["location"] not in travel_times[current_location]:
            continue
        t_travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + t_travel
        # The meeting can only start after arrival and the friend's available start.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if we can finish the meeting before the friend leaves.
        if meeting_end <= friend["avail_end"]:
            # Build the meeting schedule entry.
            schedule_entry = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_schedule = current_schedule + [schedule_entry]
            # Remove this friend from remaining.
            new_remaining = remaining[:i] + remaining[i+1:]
            # Recurse from the friend's location and the time after meeting ends.
            search(meeting_end, friend["location"], new_remaining, new_schedule)

# Start at Financial District at 9:00 AM (9*60 = 540 minutes).
start_time = 9 * 60  # 9:00 AM in minutes
start_location = "Financial District"

# Begin recursive search.
search(start_time, start_location, friends, [])

# Prepare the output JSON.
result = {"itinerary": best_itinerary}

# Output the JSON result.
print(json.dumps(result, indent=2))