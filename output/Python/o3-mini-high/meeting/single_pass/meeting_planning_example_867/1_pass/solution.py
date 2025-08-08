#!/usr/bin/env python3
import json

def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times (in minutes) between neighborhoods
travel_times = {
    "Haight-Ashbury": {
        "Mission District": 11,
        "Union Square": 19,
        "Pacific Heights": 12,
        "Bayview": 18,
        "Fisherman's Wharf": 23,
        "Marina District": 17,
        "Richmond District": 10,
        "Sunset District": 15,
        "Golden Gate Park": 7
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Union Square": 15,
        "Pacific Heights": 16,
        "Bayview": 14,
        "Fisherman's Wharf": 22,
        "Marina District": 19,
        "Richmond District": 20,
        "Sunset District": 24,
        "Golden Gate Park": 17
    },
    "Union Square": {
        "Haight-Ashbury": 18,
        "Mission District": 14,
        "Pacific Heights": 15,
        "Bayview": 15,
        "Fisherman's Wharf": 15,
        "Marina District": 18,
        "Richmond District": 20,
        "Sunset District": 27,
        "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Union Square": 12,
        "Bayview": 22,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Richmond District": 12,
        "Sunset District": 21,
        "Golden Gate Park": 15
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Union Square": 18,
        "Pacific Heights": 23,
        "Fisherman's Wharf": 25,
        "Marina District": 27,
        "Richmond District": 25,
        "Sunset District": 23,
        "Golden Gate Park": 22
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Union Square": 13,
        "Pacific Heights": 12,
        "Bayview": 26,
        "Marina District": 9,
        "Richmond District": 18,
        "Sunset District": 27,
        "Golden Gate Park": 25
    },
    "Marina District": {
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Union Square": 16,
        "Pacific Heights": 7,
        "Bayview": 27,
        "Fisherman's Wharf": 10,
        "Richmond District": 11,
        "Sunset District": 19,
        "Golden Gate Park": 18
    },
    "Richmond District": {
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Union Square": 21,
        "Pacific Heights": 10,
        "Bayview": 27,
        "Fisherman's Wharf": 18,
        "Marina District": 9,
        "Sunset District": 11,
        "Golden Gate Park": 9
    },
    "Sunset District": {
        "Haight-Ashbury": 15,
        "Mission District": 25,
        "Union Square": 30,
        "Pacific Heights": 21,
        "Bayview": 22,
        "Fisherman's Wharf": 29,
        "Marina District": 21,
        "Richmond District": 12,
        "Golden Gate Park": 11
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Mission District": 17,
        "Union Square": 22,
        "Pacific Heights": 16,
        "Bayview": 23,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Richmond District": 7,
        "Sunset District": 10
    }
}

# Friend meeting constraints:
# Times are represented as minutes from midnight.
# 9:00 AM => 540 minutes.
friends = [
    {
        "name": "Elizabeth",
        "location": "Mission District",
        "avail_start": 10 * 60 + 30,  # 10:30 -> 630
        "avail_end": 20 * 60,         # 20:00 -> 1200
        "duration": 90
    },
    {
        "name": "David",
        "location": "Union Square",
        "avail_start": 15 * 60 + 15,  # 15:15 -> 915
        "avail_end": 19 * 60,         # 19:00 -> 1140
        "duration": 45
    },
    {
        "name": "Sandra",
        "location": "Pacific Heights",
        "avail_start": 7 * 60,        # 7:00 -> 420
        "avail_end": 20 * 60,         # 20:00 -> 1200
        "duration": 120
    },
    {
        "name": "Thomas",
        "location": "Bayview",
        "avail_start": 19 * 60 + 30,  # 19:30 -> 1170
        "avail_end": 20 * 60 + 30,    # 20:30 -> 1230
        "duration": 30
    },
    {
        "name": "Robert",
        "location": "Fisherman's Wharf",
        "avail_start": 10 * 60,       # 10:00 -> 600
        "avail_end": 15 * 60,         # 15:00 -> 900
        "duration": 15
    },
    {
        "name": "Kenneth",
        "location": "Marina District",
        "avail_start": 10 * 60 + 45,  # 10:45 -> 645
        "avail_end": 13 * 60,         # 13:00 -> 780
        "duration": 45
    },
    {
        "name": "Melissa",
        "location": "Richmond District",
        "avail_start": 18 * 60 + 15,  # 18:15 -> 1095
        "avail_end": 20 * 60,         # 20:00 -> 1200
        "duration": 15
    },
    {
        "name": "Kimberly",
        "location": "Sunset District",
        "avail_start": 10 * 60 + 15,  # 10:15 -> 615
        "avail_end": 18 * 60 + 15,    # 18:15 -> 1095
        "duration": 105
    },
    {
        "name": "Amanda",
        "location": "Golden Gate Park",
        "avail_start": 7 * 60 + 45,   # 7:45 -> 465
        "avail_end": 18 * 60 + 45,    # 18:45 -> 1125
        "duration": 15
    }
]

# Global variables to store the best schedule found
best_schedule = []
best_count = 0

def dfs(curr_time, curr_loc, remaining, current_schedule):
    global best_schedule, best_count
    # Update best schedule if current itinerary is longer
    if len(current_schedule) > best_count:
        best_count = len(current_schedule)
        best_schedule = current_schedule[:]
    # Try scheduling each remaining friend's meeting next
    for i, friend in enumerate(remaining):
        travel_time = travel_times[curr_loc][friend["location"]]
        arrival_time = curr_time + travel_time
        # Wait if arriving before friend's available start
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        if meeting_end <= friend["avail_end"]:
            entry = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            }
            new_remaining = remaining[:i] + remaining[i+1:]
            dfs(meeting_end, friend["location"], new_remaining, current_schedule + [entry])

def main():
    # You arrive at Haight-Ashbury at 9:00 AM (540 minutes)
    start_time = 540
    start_location = "Haight-Ashbury"
    dfs(start_time, start_location, friends, [])
    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()