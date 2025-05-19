#!/usr/bin/env python3
import json
import copy

# Helper: convert time in minutes since midnight to H:MM format (24h, no leading zero for hour)
def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times dictionary (in minutes) as provided.
travel_times = {
    "Presidio": {
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Fisherman's Wharf": 19,
        "Marina District": 11,
        "Alamo Square": 19,
        "Sunset District": 15,
        "Nob Hill": 18,
        "North Beach": 18
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Alamo Square": 10,
        "Sunset District": 21,
        "Nob Hill": 8,
        "North Beach": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Pacific Heights": 16,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Alamo Square": 9,
        "Sunset District": 10,
        "Nob Hill": 20,
        "North Beach": 23
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Pacific Heights": 12,
        "Golden Gate Park": 25,
        "Marina District": 9,
        "Alamo Square": 21,
        "Sunset District": 27,
        "Nob Hill": 11,
        "North Beach": 6
    },
    "Marina District": {
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Fisherman's Wharf": 10,
        "Alamo Square": 15,
        "Sunset District": 19,
        "Nob Hill": 12,
        "North Beach": 11
    },
    "Alamo Square": {
        "Presidio": 17,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Fisherman's Wharf": 19,
        "Marina District": 15,
        "Sunset District": 16,
        "Nob Hill": 11,
        "North Beach": 15
    },
    "Sunset District": {
        "Presidio": 16,
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "Marina District": 21,
        "Alamo Square": 17,
        "Nob Hill": 27,
        "North Beach": 28
    },
    "Nob Hill": {
        "Presidio": 17,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Fisherman's Wharf": 10,
        "Marina District": 11,
        "Alamo Square": 11,
        "Sunset District": 24,
        "North Beach": 8
    },
    "North Beach": {
        "Presidio": 17,
        "Pacific Heights": 8,
        "Golden Gate Park": 22,
        "Fisherman's Wharf": 5,
        "Marina District": 9,
        "Alamo Square": 16,
        "Sunset District": 27,
        "Nob Hill": 7
    }
}

# Meetings: each meeting has a location, availability window (in minutes since midnight), and required minimum meeting duration.
# Times are converted from the given times.
# Kevin: available at Pacific Heights from 7:15 (435) to 8:45 (525), need 90 minutes.
# Michelle: Golden Gate Park from 20:00 (1200) to 21:00 (1260), need 15 minutes.
# Emily: Fisherman's Wharf from 16:15 (975) to 19:00 (1140), need 30 minutes.
# Mark: Marina District from 18:15 (1095) to 19:45 (1185), need 75 minutes.
# Barbara: Alamo Square from 17:00 (1020) to 19:00 (1140), need 120 minutes.
# Laura: Sunset District from 19:00 (1140) to 21:15 (1275), need 75 minutes.
# Mary: Nob Hill from 17:30 (1050) to 19:00 (1140), need 45 minutes.
# Helen: North Beach from 11:00 (660) to 12:15 (735), need 45 minutes.
meetings = {
    "Kevin": {
        "location": "Pacific Heights",
        "window_start": 435,
        "window_end": 525,
        "duration": 90
    },
    "Michelle": {
        "location": "Golden Gate Park",
        "window_start": 1200,
        "window_end": 1260,
        "duration": 15
    },
    "Emily": {
        "location": "Fisherman's Wharf",
        "window_start": 975,
        "window_end": 1140,
        "duration": 30
    },
    "Mark": {
        "location": "Marina District",
        "window_start": 1095,
        "window_end": 1185,
        "duration": 75
    },
    "Barbara": {
        "location": "Alamo Square",
        "window_start": 1020,
        "window_end": 1140,
        "duration": 120
    },
    "Laura": {
        "location": "Sunset District",
        "window_start": 1140,
        "window_end": 1275,
        "duration": 75
    },
    "Mary": {
        "location": "Nob Hill",
        "window_start": 1050,
        "window_end": 1140,
        "duration": 45
    },
    "Helen": {
        "location": "North Beach",
        "window_start": 660,
        "window_end": 735,
        "duration": 45
    }
}

# Starting conditions: arrive at Presidio at 9:00 (540 minutes)
start_location = "Presidio"
start_time = 540

# We'll perform DFS to try all orders of meetings that can be feasibly scheduled,
# taking into account travel times, meeting time windows, and required durations.
best_itinerary = []
best_count = 0

def dfs(current_time, current_location, remaining_meetings, current_itinerary):
    global best_itinerary, best_count
    # At each step, if no remaining meeting can be scheduled, update best solution if necessary.
    if len(current_itinerary) > best_count:
        best_itinerary = copy.deepcopy(current_itinerary)
        best_count = len(current_itinerary)
    
    # Try each remaining meeting
    for person, info in remaining_meetings.items():
        destination = info["location"]
        # Get travel time from current_location to destination
        if current_location == destination:
            travel = 0
        else:
            travel = travel_times[current_location][destination]
        arrival_time = current_time + travel
        # Meeting can only start when both arrived and the meeting window starts.
        meeting_start = max(arrival_time, info["window_start"])
        meeting_end = meeting_start + info["duration"]
        # Check if meeting can finish within the meeting's availability window.
        if meeting_end <= info["window_end"]:
            # Create a new itinerary entry
            entry = {
                "action": "meet",
                "location": destination,
                "person": person,
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            }
            # Prepare new state
            new_itinerary = current_itinerary + [entry]
            new_remaining = remaining_meetings.copy()
            del new_remaining[person]
            dfs(meeting_end, destination, new_remaining, new_itinerary)

# Start DFS from the starting point.
dfs(start_time, start_location, meetings, [])

# Prepare result JSON dictionary.
result = {
    "itinerary": best_itinerary
}

# Output the result as JSON
print(json.dumps(result, indent=2))