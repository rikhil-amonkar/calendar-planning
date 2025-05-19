#!/usr/bin/env python3
import json
from copy import deepcopy

# Helper functions to convert time formats
def time_to_minutes(time_str):
    # time_str format: "H:MM" in 24hr format (e.g., "9:00", "13:30")
    parts = time_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel times dictionary (in minutes)
travel_times = {
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Bayview"): 23,
    
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,
    
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 22,
    
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Bayview"): 22,
    
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 26,
    
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Bayview"): 26,
    
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,
}

# Meeting constraints for each friend.
# Times are in minutes from midnight.
meetings = [
    {
        "person": "Matthew",
        "location": "Presidio",
        "avail_start": time_to_minutes("11:00"),
        "avail_end": time_to_minutes("21:00"),
        "duration": 90
    },
    {
        "person": "Margaret",
        "location": "Chinatown",
        "avail_start": time_to_minutes("9:15"),
        "avail_end": time_to_minutes("18:45"),
        "duration": 90
    },
    {
        "person": "Nancy",
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("14:15"),
        "avail_end": time_to_minutes("17:00"),
        "duration": 15
    },
    {
        "person": "Helen",
        "location": "Richmond District",
        "avail_start": time_to_minutes("19:45"),
        "avail_end": time_to_minutes("22:00"),
        "duration": 60
    },
    {
        "person": "Rebecca",
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("21:15"),
        "avail_end": time_to_minutes("22:15"),
        "duration": 60
    },
    {
        "person": "Kimberly",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("13:00"),
        "avail_end": time_to_minutes("16:30"),
        "duration": 120
    },
    {
        "person": "Kenneth",
        "location": "Bayview",
        "avail_start": time_to_minutes("14:30"),
        "avail_end": time_to_minutes("18:00"),
        "duration": 60
    }
]

# Starting conditions
start_location = "Russian Hill"
start_time = time_to_minutes("9:00")

# Global variable to store the best itinerary (max meetings scheduled)
best_itinerary = []

def backtrack(curr_loc, curr_time, remaining, itinerary):
    global best_itinerary
    # Update best itinerary if current itinerary has more meetings
    if len(itinerary) > len(best_itinerary):
        best_itinerary = deepcopy(itinerary)
    
    # Try scheduling each remaining meeting next
    for i, meeting in enumerate(remaining):
        # Check travel time from current location to meeting location
        key = (curr_loc, meeting["location"])
        if key not in travel_times:
            continue  # if route not defined, skip
        travel_time = travel_times[key]
        arrival_time = curr_time + travel_time
        # The meeting can start when both you arrive and when the friend is available.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if the meeting can finish before the friend's availability ends.
        if meeting_end <= meeting["avail_end"]:
            # Create an itinerary entry
            entry = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_itinerary = itinerary + [entry]
            # Prepare new remaining list (remove the meeting we just scheduled)
            new_remaining = remaining[:i] + remaining[i+1:]
            # Recurse from the meeting's location and end time.
            backtrack(meeting["location"], meeting_end, new_remaining, new_itinerary)

if __name__ == "__main__":
    # Begin backtracking search from starting location and time
    backtrack(start_location, start_time, meetings, [])

    # Prepare final output JSON object
    output = {"itinerary": best_itinerary}
    # Print JSON formatted output
    print(json.dumps(output, indent=2))