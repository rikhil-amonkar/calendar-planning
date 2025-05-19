#!/usr/bin/env python3
import json

def time_to_minutes(time_str):
    # time_str expected in format "H:MM" (24-hour) 
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(m):
    # Convert minutes since midnight to "H:MM" (24-hour) without a leading zero for hours.
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define meeting constraints and availability in minutes since midnight.
# Each meeting is defined as: person, location, available_start, available_end, required_duration (in minutes)
meetings = [
    { "person": "Nancy", "location": "Nob Hill", 
      "avail_start": time_to_minutes("8:15"), "avail_end": time_to_minutes("12:45"), "duration": 90 },
    { "person": "Stephanie", "location": "Haight-Ashbury", 
      "avail_start": time_to_minutes("10:15"), "avail_end": time_to_minutes("12:15"), "duration": 75 },
    { "person": "Robert", "location": "Financial District", 
      "avail_start": time_to_minutes("13:15"), "avail_end": time_to_minutes("15:15"), "duration": 45 },
    { "person": "Brian", "location": "Embarcadero", 
      "avail_start": time_to_minutes("14:15"), "avail_end": time_to_minutes("16:00"), "duration": 105 },
    { "person": "Melissa", "location": "Richmond District", 
      "avail_start": time_to_minutes("14:00"), "avail_end": time_to_minutes("19:30"), "duration": 30 },
    { "person": "Sarah", "location": "Golden Gate Park", 
      "avail_start": time_to_minutes("17:00"), "avail_end": time_to_minutes("19:15"), "duration": 75 },
    { "person": "Steven", "location": "North Beach", 
      "avail_start": time_to_minutes("17:30"), "avail_end": time_to_minutes("20:30"), "duration": 15 },
    { "person": "Elizabeth", "location": "Union Square", 
      "avail_start": time_to_minutes("11:30"), "avail_end": time_to_minutes("21:00"), "duration": 60 },
    # David and James are not scheduled because of conflicting time windows.
]

# Pre-defined travel times in minutes between locations (only the ones needed for our itinerary)
# The itinerary order will be:
# Start at "The Castro" -> Nob Hill -> Haight-Ashbury -> Financial District ->
# Embarcadero -> Richmond District -> Golden Gate Park -> North Beach -> Union Square
travel_times = {
    ("The Castro", "Nob Hill"): 16,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Financial District", "Embarcadero"): 4,
    ("Embarcadero", "Richmond District"): 21,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Golden Gate Park", "North Beach"): 23,
    ("North Beach", "Union Square"): 7,
}

# We'll compute the itinerary step-by-step.
# Start: arriving at "The Castro" at 9:00 AM.
current_time = time_to_minutes("9:00")
current_location = "The Castro"

itinerary = []

def schedule_meeting(meeting, depart_time, depart_location, travel_times):
    # Calculate travel time from depart_location to meeting location
    travel = travel_times.get((depart_location, meeting["location"]))
    if travel is None:
        # If not found explicitly, try reverse (assuming symmetry if not provided)
        travel = travel_times.get((meeting["location"], depart_location))
        if travel is None:
            raise ValueError(f"No travel time available from {depart_location} to {meeting['location']}")
    arrival_time = depart_time + travel
    # The meeting can only start when both you have arrived and the person's available window has begun.
    meeting_start = max(arrival_time, meeting["avail_start"])
    meeting_end = meeting_start + meeting["duration"]
    if meeting_end > meeting["avail_end"]:
        raise ValueError(f"Cannot schedule meeting with {meeting['person']} within their available window.")
    # Return the meeting schedule and the new current time and location
    return {
        "action": "meet",
        "location": meeting["location"],
        "person": meeting["person"],
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    }, meeting_end, meeting["location"]

# Compute the itinerary in the chosen order.
# Order: Nancy (Nob Hill), Stephanie (Haight-Ashbury), Robert (Financial District),
# Brian (Embarcadero), Melissa (Richmond District), Sarah (Golden Gate Park),
# Steven (North Beach), Elizabeth (Union Square)

order = ["Nancy", "Stephanie", "Robert", "Brian", "Melissa", "Sarah", "Steven", "Elizabeth"]

# Create a lookup dictionary for meetings by person
meeting_lookup = {m["person"]: m for m in meetings}

for person in order:
    meeting = meeting_lookup[person]
    entry, new_time, new_loc = schedule_meeting(meeting, current_time, current_location, travel_times)
    itinerary.append(entry)
    current_time = new_time
    current_location = new_loc

# Output the itinerary as a JSON-formatted dictionary.
result = {
    "itinerary": itinerary
}
print(json.dumps(result, indent=2))