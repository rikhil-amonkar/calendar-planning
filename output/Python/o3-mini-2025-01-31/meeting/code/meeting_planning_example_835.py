#!/usr/bin/env python3
import json
import sys

# Convert time in minutes (since midnight) to a string H:MM in 24-hour format.
def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times data as a nested dictionary.
travel_times = {
    "Pacific Heights": {
        "Golden Gate Park": 15,
        "The Castro": 16,
        "Bayview": 22,
        "Marina District": 6,
        "Union Square": 12,
        "Sunset District": 21,
        "Alamo Square": 10,
        "Financial District": 13,
        "Mission District": 15
    },
    "Golden Gate Park": {
        "Pacific Heights": 16,
        "The Castro": 13,
        "Bayview": 23,
        "Marina District": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "Mission District": 17
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Marina District": 21,
        "Union Square": 19,
        "Sunset District": 17,
        "Alamo Square": 8,
        "Financial District": 21,
        "Mission District": 7
    },
    "Bayview": {
        "Pacific Heights": 23,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Marina District": 27,
        "Union Square": 18,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "Mission District": 13
    },
    "Marina District": {
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Union Square": 16,
        "Sunset District": 19,
        "Alamo Square": 15,
        "Financial District": 17,
        "Mission District": 20
    },
    "Union Square": {
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "The Castro": 17,
        "Bayview": 15,
        "Marina District": 18,
        "Sunset District": 27,
        "Alamo Square": 15,
        "Financial District": 9,
        "Mission District": 14
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Marina District": 21,
        "Union Square": 30,
        "Alamo Square": 17,
        "Financial District": 30,
        "Mission District": 25
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Marina District": 15,
        "Union Square": 14,
        "Sunset District": 16,
        "Financial District": 17,
        "Mission District": 10
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Marina District": 15,
        "Union Square": 9,
        "Sunset District": 30,
        "Alamo Square": 17,
        "Mission District": 15
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "The Castro": 7,
        "Bayview": 14,
        "Marina District": 19,
        "Union Square": 15,
        "Sunset District": 24,
        "Alamo Square": 11,
        "Financial District": 15
    }
}

# Define the meeting constraints as a list of dictionaries.
# Times are in minutes from midnight.
meetings = [
    {
        "person": "Helen",
        "location": "Golden Gate Park",
        "avail_start": 9*60 + 30,   # 9:30
        "avail_end": 12*60 + 15,    # 12:15
        "min_duration": 45
    },
    {
        "person": "Steven",
        "location": "The Castro",
        "avail_start": 20*60 + 15,  # 20:15
        "avail_end": 22*60,         # 22:00
        "min_duration": 105
    },
    {
        "person": "Deborah",
        "location": "Bayview",
        "avail_start": 8*60 + 30,   # 8:30
        "avail_end": 12*60,         # 12:00
        "min_duration": 30
    },
    {
        "person": "Matthew",
        "location": "Marina District",
        "avail_start": 9*60 + 15,   # 9:15
        "avail_end": 14*60 + 15,    # 14:15
        "min_duration": 45
    },
    {
        "person": "Joseph",
        "location": "Union Square",
        "avail_start": 14*60 + 15,  # 14:15
        "avail_end": 18*60 + 45,    # 18:45
        "min_duration": 120
    },
    {
        "person": "Ronald",
        "location": "Sunset District",
        "avail_start": 16*60,       # 16:00
        "avail_end": 20*60 + 45,     # 20:45
        "min_duration": 60
    },
    {
        "person": "Robert",
        "location": "Alamo Square",
        "avail_start": 18*60 + 30,   # 18:30
        "avail_end": 21*60 + 15,     # 21:15
        "min_duration": 120
    },
    {
        "person": "Rebecca",
        "location": "Financial District",
        "avail_start": 14*60 + 45,   # 14:45
        "avail_end": 16*60 + 15,     # 16:15
        "min_duration": 30
    },
    {
        "person": "Elizabeth",
        "location": "Mission District",
        "avail_start": 18*60 + 30,   # 18:30
        "avail_end": 21*60,          # 21:00
        "min_duration": 120
    }
]

# Initial start: arriving at Pacific Heights at 9:00.
start_time = 9 * 60  # 540 minutes
start_location = "Pacific Heights"

# We'll perform a depth-first search to try all orders meeting feasibility.
# We want to maximize the number of meetings scheduled.
best_schedule = []
best_count = 0

def dfs(current_time, current_location, remaining_meetings, current_itinerary):
    global best_schedule, best_count
    # If current itinerary is better than best so far, update.
    if len(current_itinerary) > best_count:
        best_count = len(current_itinerary)
        best_schedule = current_itinerary[:]
    # Try each remaining meeting.
    for i, meeting in enumerate(remaining_meetings):
        # Get travel time from current location to meeting's location.
        if current_location not in travel_times or meeting["location"] not in travel_times[current_location]:
            continue  # no route defined
        travel_time = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel_time
        # The meeting can only start at max(arrival_time, avail_start).
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["min_duration"]
        # Check if meeting_end is within the available window.
        if meeting_end > meeting["avail_end"]:
            continue  # Cannot meet this friend.
        # Create an itinerary entry
        entry = {
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
        # Prepare new itinerary and remaining meetings.
        new_itinerary = current_itinerary + [entry]
        new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
        # Continue search from the end of this meeting.
        dfs(meeting_end, meeting["location"], new_remaining, new_itinerary)

def main():
    global best_schedule, best_count
    dfs(start_time, start_location, meetings, [])
    # Prepare JSON output structure.
    output = { "itinerary": best_schedule }
    # Print JSON-formatted output.
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()