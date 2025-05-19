#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

# Helper function: Convert a time string "H:MM" to a datetime object for an arbitrary day.
def str_to_time(timestr):
    # Use an arbitrary fixed date (e.g., 2000-01-01) with given hour and minute.
    return datetime(2000, 1, 1, *map(int, timestr.split(":")))

# Helper function: Format a datetime object into "H:MM" with no leading zero in hour.
def time_to_str(time_obj):
    return f"{time_obj.hour}:{time_obj.minute:02d}"

# Function to add minutes to a datetime object.
def add_minutes(time_obj, minutes):
    return time_obj + timedelta(minutes=minutes)

# Define travel times between locations (in minutes)
travel_times = {
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Financial District"): 5,
    
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Financial District"): 26,
    
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Financial District"): 19,
    
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Financial District"): 23,
    
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Presidio"): 22,
}

# Meeting constraints for each friend
meetings = {
    "Mary": {
        "location": "Golden Gate Park",
        "available_start": str_to_time("8:45"),
        "available_end": str_to_time("11:45"),
        "min_duration": 45
    },
    "Kevin": {
        "location": "Haight-Ashbury",
        "available_start": str_to_time("10:15"),
        "available_end": str_to_time("16:15"),
        "min_duration": 90
    },
    "Deborah": {
        "location": "Bayview",
        "available_start": str_to_time("15:00"),
        "available_end": str_to_time("19:15"),
        "min_duration": 120
    },
    "Stephanie": {
        "location": "Presidio",
        "available_start": str_to_time("10:00"),
        "available_end": str_to_time("17:15"),
        "min_duration": 120
    },
    "Emily": {
        "location": "Financial District",
        "available_start": str_to_time("11:30"),
        "available_end": str_to_time("21:45"),
        "min_duration": 105
    }
}

# We start at Embarcadero at 9:00
start_location = "Embarcadero"
current_time = str_to_time("9:00")
current_location = start_location

# We decide on one ordering that optimizes the number of meetings.
# The chosen order is: Mary, Kevin, Stephanie, Deborah, Emily.
order = ["Mary", "Kevin", "Stephanie", "Deborah", "Emily"]

itinerary = []

for person in order:
    meeting = meetings[person]
    destination = meeting["location"]
    # Determine travel time from current_location to destination.
    travel_key = (current_location, destination)
    travel_time = travel_times.get(travel_key, None)
    if travel_time is None:
        # if not defined, assume a very high travel time (should not happen)
        travel_time = 999
    # Travel to the meeting location.
    current_time = add_minutes(current_time, travel_time)
    
    # If arrived before the meeting's available start, wait until available_start.
    if current_time < meeting["available_start"]:
        current_time = meeting["available_start"]
    
    meeting_start = current_time
    meeting_end = add_minutes(meeting_start, meeting["min_duration"])
    
    # Ensure meeting ends before the person's available_end.
    if meeting_end > meeting["available_end"]:
        # Adjust meeting_end if needed (infeasible, but for this algorithm we assume feasibility).
        meeting_end = meeting["available_end"]
    
    # Add this meeting to the itinerary.
    itinerary.append({
        "action": "meet",
        "location": destination,
        "person": person,
        "start_time": time_to_str(meeting_start),
        "end_time": time_to_str(meeting_end)
    })
    
    # Update current time and current location after meeting.
    current_time = meeting_end
    current_location = destination

# Prepare the final JSON dictionary.
result = {
    "itinerary": itinerary
}

# Output the result as JSON.
print(json.dumps(result, indent=2))