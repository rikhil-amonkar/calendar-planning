#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

# Helper functions to convert times between "H:MM" format and minutes since midnight.
def time_to_minutes(t_str):
    # t_str format "H:MM" (24-hour, no leading zero necessary)
    h, m = map(int, t_str.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

# Travel times dictionary based on the given input.
# For simplicity, the keys are the names of the locations.
travel_times = {
    "The Castro": {
        "Alamo Square": 8,
        "Richmond District": 16,
        "Financial District": 21,
        "Union Square": 19,
        "Fisherman's Wharf": 24,
        "Marina District": 21,
        "Haight-Ashbury": 6,
        "Mission District": 7,
        "Pacific Heights": 16,
        "Golden Gate Park": 11
    },
    "Alamo Square": {
        "The Castro": 8,
        "Richmond District": 11,
        "Financial District": 17,
        "Union Square": 14,
        "Fisherman's Wharf": 19,
        "Marina District": 15,
        "Haight-Ashbury": 5,
        "Mission District": 10,
        "Pacific Heights": 10,
        "Golden Gate Park": 9
    },
    "Richmond District": {
        "The Castro": 16,
        "Alamo Square": 13,
        "Financial District": 22,
        "Union Square": 21,
        "Fisherman's Wharf": 18,
        "Marina District": 9,
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Pacific Heights": 10,
        "Golden Gate Park": 9
    },
    "Financial District": {
        "The Castro": 20,
        "Alamo Square": 17,
        "Richmond District": 21,
        "Union Square": 9,
        "Fisherman's Wharf": 10,
        "Marina District": 15,
        "Haight-Ashbury": 19,
        "Mission District": 17,
        "Pacific Heights": 13,
        "Golden Gate Park": 23
    },
    "Union Square": {
        "The Castro": 17,
        "Alamo Square": 15,
        "Richmond District": 20,
        "Financial District": 9,
        "Fisherman's Wharf": 15,
        "Marina District": 18,
        "Haight-Ashbury": 18,
        "Mission District": 14,
        "Pacific Heights": 15,
        "Golden Gate Park": 22
    },
    "Fisherman's Wharf": {
        "The Castro": 27,
        "Alamo Square": 21,
        "Richmond District": 18,
        "Financial District": 11,
        "Union Square": 13,
        "Marina District": 9,
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Pacific Heights": 12,
        "Golden Gate Park": 25
    },
    "Marina District": {
        "The Castro": 22,
        "Alamo Square": 15,
        "Richmond District": 11,
        "Financial District": 17,
        "Union Square": 16,
        "Fisherman's Wharf": 10,
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Pacific Heights": 7,
        "Golden Gate Park": 18
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "Alamo Square": 5,
        "Richmond District": 10,
        "Financial District": 21,
        "Union Square": 19,
        "Fisherman's Wharf": 23,
        "Marina District": 17,
        "Mission District": 11,
        "Pacific Heights": 12,
        "Golden Gate Park": 7
    },
    "Mission District": {
        "The Castro": 7,
        "Alamo Square": 11,
        "Richmond District": 20,
        "Financial District": 15,
        "Union Square": 15,
        "Fisherman's Wharf": 22,
        "Marina District": 19,
        "Haight-Ashbury": 12,
        "Pacific Heights": 16,
        "Golden Gate Park": 17
    },
    "Pacific Heights": {
        "The Castro": 16,
        "Alamo Square": 10,
        "Richmond District": 12,
        "Financial District": 13,
        "Union Square": 12,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Golden Gate Park": 15
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Alamo Square": 9,
        "Richmond District": 7,
        "Financial District": 26,
        "Union Square": 22,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Haight-Ashbury": 7,
        "Mission District": 17,
        "Pacific Heights": 16
    }
}

# Meeting constraints for each friend.
# Each meeting is represented as a dictionary with:
# - person: Name
# - location: Meeting location
# - window_start: earliest available time (in minutes since midnight)
# - window_end: latest available time (in minutes since midnight)
# - duration: minimum meeting duration (in minutes)
meetings = [
    {"person": "Anthony", "location": "Haight-Ashbury", "window_start": time_to_minutes("7:15"), "window_end": time_to_minutes("10:30"), "duration": 30},
    {"person": "Helen", "location": "Pacific Heights", "window_start": time_to_minutes("8:00"), "window_end": time_to_minutes("12:00"), "duration": 75},
    {"person": "Joshua", "location": "Richmond District", "window_start": time_to_minutes("7:00"), "window_end": time_to_minutes("20:00"), "duration": 15},
    {"person": "Karen", "location": "Marina District", "window_start": time_to_minutes("11:30"), "window_end": time_to_minutes("18:30"), "duration": 15},
    {"person": "Joseph", "location": "Financial District", "window_start": time_to_minutes("11:15"), "window_end": time_to_minutes("13:30"), "duration": 15},
    {"person": "Brian", "location": "Fisherman's Wharf", "window_start": time_to_minutes("13:45"), "window_end": time_to_minutes("20:45"), "duration": 105},
    # For the later time slot, we have a scheduling conflict between William and David.
    # To maximize the number of meetings, we choose one; here we pick William.
    {"person": "William", "location": "Alamo Square", "window_start": time_to_minutes("15:15"), "window_end": time_to_minutes("17:15"), "duration": 60},
    {"person": "Matthew", "location": "Mission District", "window_start": time_to_minutes("17:15"), "window_end": time_to_minutes("19:15"), "duration": 120},
    {"person": "Jeffrey", "location": "Golden Gate Park", "window_start": time_to_minutes("19:00"), "window_end": time_to_minutes("21:30"), "duration": 60}
]

# Starting parameters: we arrive at The Castro at 9:00AM
current_location = "The Castro"
current_time = time_to_minutes("9:00")

itinerary = []

# Process each meeting in the defined order.
for mtg in meetings:
    # Calculate travel time from current_location to the meeting's location.
    # If current_location equals meeting location (unlikely), travel time is 0.
    if current_location == mtg["location"]:
        travel_time = 0
    else:
        travel_time = travel_times[current_location][mtg["location"]]
    arrival_time = current_time + travel_time

    # Meeting start is the later of arrival time and the person's available window start.
    meeting_start = max(arrival_time, mtg["window_start"])
    meeting_end = meeting_start + mtg["duration"]

    # Check if the meeting can be completed within the person's available window.
    if meeting_end > mtg["window_end"]:
        # If we cannot schedule the meeting then skip.
        continue

    # Append the meeting action to the itinerary.
    itinerary.append({
        "action": "meet",
        "location": mtg["location"],
        "person": mtg["person"],
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })

    # Update current location and time.
    current_location = mtg["location"]
    current_time = meeting_end

# Output the itinerary as a JSON-formatted dictionary.
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))