#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

# Helper function to convert time (in minutes since midnight) to H:MM string (24-hour format, no leading zero on hour)
def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Convert a time string "H:MM" to minutes since midnight.
def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    mins = int(parts[1])
    return hours * 60 + mins

# Input parameters as variables
arrival_location = "Sunset District"
arrival_time_str = "9:00"  # arrival at Sunset District

# Joshua's meeting constraints
joshua_location = "Golden Gate Park"
joshua_available_start_str = "20:45"  # 8:45PM in 24-hour
joshua_available_end_str = "21:45"    # 9:45PM in 24-hour
minimum_meeting_duration = 15  # in minutes

# Travel times (in minutes)
travel_Sunset_to_GGP = 11  # from Sunset District to Golden Gate Park
travel_GGP_to_Sunset = 10  # from Golden Gate Park to Sunset District

# Convert times to minutes since midnight for computation
arrival_time = time_str_to_minutes(arrival_time_str)
joshua_available_start = time_str_to_minutes(joshua_available_start_str)
joshua_available_end = time_str_to_minutes(joshua_available_end_str)

# Calculate the optimal departure time from Sunset District to reach Golden Gate Park
# We want to arrive exactly at or just in time for Joshua's availability start.
# To ensure we arrive by joshua_available_start, we subtract the travel time.
departure_time = joshua_available_start - travel_Sunset_to_GGP

# Safety check: if departure time is before our arrival at Sunset District, then we set the departure time to our arrival
if departure_time < arrival_time:
    departure_time = arrival_time

# Calculate the meeting start time at Golden Gate Park. Ideally, as soon as Joshua is available.
# If we arrive early we would wait, so meeting start is max(arrival_at_GGP, joshua_available_start).
arrival_at_GGP = departure_time + travel_Sunset_to_GGP
meeting_start = max(arrival_at_GGP, joshua_available_start)

# Calculate meeting end time ensuring minimum duration is met but not exceeding Joshua's availability.
proposed_meeting_end = meeting_start + minimum_meeting_duration
if proposed_meeting_end > joshua_available_end:
    # If the meeting cannot be scheduled to meet the minimum duration, then there is no valid schedule.
    itinerary = {"itinerary": []}
else:
    meeting_end = proposed_meeting_end

    # Build the itinerary. In this simple scenario, the itinerary includes the single meeting.
    itinerary = {
        "itinerary": [
            {
                "action": "meet",
                "location": joshua_location,
                "person": "Joshua",
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            }
        ]
    }

# Output the result as a JSON-formatted dictionary.
print(json.dumps(itinerary, indent=2))