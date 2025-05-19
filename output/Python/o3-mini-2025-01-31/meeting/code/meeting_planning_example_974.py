#!/usr/bin/env python3
import json

def time_to_minutes(time_str):
    # time_str format "H:MM" (24-hour, no leading zero necessarily)
    parts = time_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define travel times for the legs we use in the itinerary.
# The keys are the origin neighborhoods and the sub-dict keys are destination neighborhoods.
travel_times = {
    "Sunset District": {
        "Richmond District": 12,
    },
    "Richmond District": {
        "Presidio": 7,
    },
    "Presidio": {
        "Nob Hill": 18,
    },
    "Nob Hill": {
        "Marina District": 11,
    },
    "Marina District": {
        "Mission District": 19,
    },
    "Mission District": {
        "Alamo Square": 11,
    }
}

# Define the meeting constraints for each friend.
# Each meeting constraint is a dictionary with:
# - person: friend name
# - location: where to meet
# - available_start: earliest meeting start time (in minutes since midnight)
# - available_end: latest meeting end time (in minutes since midnight)
# - duration: minimum required meeting duration (in minutes)
meetings = [
    {
        "person": "Jeffrey",
        "location": "Richmond District",
        "available_start": time_to_minutes("12:00"),
        "available_end": time_to_minutes("19:15"),
        "duration": 45
    },
    {
        "person": "Charles",
        "location": "Presidio",
        "available_start": time_to_minutes("13:15"),
        "available_end": time_to_minutes("15:00"),
        "duration": 105
    },
    {
        "person": "Robert",
        "location": "Nob Hill",
        "available_start": time_to_minutes("13:15"),
        "available_end": time_to_minutes("17:30"),
        "duration": 90
    },
    {
        "person": "Kimberly",
        "location": "Marina District",
        "available_start": time_to_minutes("17:00"),
        "available_end": time_to_minutes("19:45"),
        "duration": 75
    },
    {
        "person": "Brian",
        "location": "Mission District",
        "available_start": time_to_minutes("15:30"),
        "available_end": time_to_minutes("22:00"),
        "duration": 60
    },
    {
        "person": "Joshua",
        "location": "Alamo Square",
        "available_start": time_to_minutes("18:45"),
        "available_end": time_to_minutes("22:00"),
        "duration": 60
    }
]

# Our chosen itinerary order is:
# 1. Jeffrey (Richmond District)
# 2. Charles (Presidio)
# 3. Robert (Nob Hill)
# 4. Kimberly (Marina District)
# 5. Brian (Mission District)
# 6. Joshua (Alamo Square)
# We start at Sunset District at 9:00.
current_time = time_to_minutes("9:00")
current_location = "Sunset District"

itinerary = []

for meeting in meetings:
    # Determine travel time from current location to the meeting location.
    # Look up the travel time in our travel_times dictionary.
    if current_location in travel_times and meeting["location"] in travel_times[current_location]:
        travel = travel_times[current_location][meeting["location"]]
    else:
        # if there is no defined travel time, assume 0 (should not happen in our planned route)
        travel = 0
        
    # Travel to the meeting location.
    current_time += travel

    # The meeting can only start at the later of arrival time or the meeting's available_start.
    meeting_start = max(current_time, meeting["available_start"])
    meeting_end = meeting_start + meeting["duration"]
    
    # Check if meeting_end exceeds the available_end time.
    if meeting_end > meeting["available_end"]:
        raise Exception(f"Cannot schedule meeting with {meeting['person']} within available window.")
        
    # Append the meeting action to the itinerary.
    itinerary.append({
        "action": "meet",
        "location": meeting["location"],
        "person": meeting["person"],
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    
    # Update current time and current location.
    current_time = meeting_end
    current_location = meeting["location"]

# Prepare the output JSON dictionary.
output = {"itinerary": itinerary}

print(json.dumps(output, indent=2))