#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

# Helper functions for time manipulation
def str_to_time(time_str):
    # time_str like "9:00" in 24h format
    return datetime.strptime(time_str, "%H:%M")

def time_to_str(dt):
    # Returns time string in H:MM format (strip leading zeros from hour)
    return f"{dt.hour}:{dt.minute:02d}"

def add_minutes(dt, minutes):
    return dt + timedelta(minutes=minutes)

# Travel times between locations (in minutes)
travel_times = {
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Golden Gate Park"): 23,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Chinatown"): 23
}

# Meeting constraints and availability
# Arrival: at Financial District at 9:00
arrival_time_fd = str_to_time("9:00")

# Barbara is at Golden Gate Park from 8:15 to 19:00, minimum meeting: 45 min.
barbara_location = "Golden Gate Park"
barbara_available_start = str_to_time("8:15")
barbara_available_end = str_to_time("19:00")
min_barbara_meeting = 45  # minutes

# Kenneth is at Chinatown from 12:00 to 15:00, minimum meeting: 90 min.
kenneth_location = "Chinatown"
kenneth_available_start = str_to_time("12:00")
kenneth_available_end = str_to_time("15:00")
min_kenneth_meeting = 90  # minutes

# Compute itinerary
itinerary = []

# Step 1: Travel from Financial District to Golden Gate Park to meet Barbara.
start_from_fd = arrival_time_fd
travel_fd_to_barbara = travel_times[("Financial District", barbara_location)]
barbara_meeting_start = add_minutes(start_from_fd, travel_fd_to_barbara)
# Make sure Barbara is available; if arrival time is before her available start, wait until available_start.
if barbara_meeting_start < barbara_available_start:
    barbara_meeting_start = barbara_available_start

# We want to eventually meet Kenneth for 90 minutes in Chinatown starting as early as possible at Kenneth's availability start.
# To arrive on time to Kenneth, we need to leave Barbara meeting by:
travel_barbara_to_kenneth = travel_times[(barbara_location, kenneth_location)]
# We need to arrive at Kenneth no earlier than his available start (12:00), so departure time from Barbara must be:
latest_departure_from_barbara = kenneth_available_start - timedelta(minutes=travel_barbara_to_kenneth)

# We want to allocate at least min_barbara_meeting with Barbara.
# Our planned Barbara meeting end time must be the minimum between:
#   (a) latest_departure_from_barbara (to catch Kenneth on time)
#   (b) what if we choose to extend? But to meet Kenneth’s minimum, we plan to start Kenneth meeting at his available start.
# So schedule Barbara meeting from barbara_meeting_start until latest_departure_from_barbara,
# but also enforce that we have at least min_barbara_meeting minutes.
proposed_barbara_end = latest_departure_from_barbara

# Check if the meeting duration is at least the minimum required.
duration_barbara = (proposed_barbara_end - barbara_meeting_start).total_seconds() / 60
if duration_barbara < min_barbara_meeting:
    # If not enough time, then we adjust by giving the minimum meeting time and then schedule Kenneth meeting later.
    proposed_barbara_end = add_minutes(barbara_meeting_start, min_barbara_meeting)
    # But then we must check if arriving at Kenneth is still possible
    arrival_at_kenneth = add_minutes(proposed_barbara_end, travel_barbara_to_kenneth)
    if arrival_at_kenneth < kenneth_available_start:
        # wait until Kenneth becomes available
        departure_delay = (kenneth_available_start - arrival_at_kenneth).total_seconds()/60
        proposed_barbara_end = add_minutes(proposed_barbara_end, int(departure_delay))
        
barbara_meeting_end = proposed_barbara_end

# Step 2: Travel from Golden Gate Park to Chinatown for Kenneth.
arrival_at_kenneth = add_minutes(barbara_meeting_end, travel_barbara_to_kenneth)
# If arrival is before Kenneth is available, then adjust start time to Kenneth_available_start.
kenneth_meeting_start = kenneth_available_start if arrival_at_kenneth < kenneth_available_start else arrival_at_kenneth

# Schedule Kenneth meeting for at least min_kenneth_meeting minutes.
kenneth_meeting_end = add_minutes(kenneth_meeting_start, min_kenneth_meeting)
# Ensure that Kenneth's meeting does not go past his available end time.
if kenneth_meeting_end > kenneth_available_end:
    # If it does, adjust meeting start to allow full required duration within his availability.
    kenneth_meeting_start = kenneth_available_end - timedelta(minutes=min_kenneth_meeting)
    kenneth_meeting_end = kenneth_available_end

# Build itinerary as list of dicts.
itinerary.append({
    "action": "meet",
    "location": barbara_location,
    "person": "Barbara",
    "start_time": time_to_str(barbara_meeting_start),
    "end_time": time_to_str(barbara_meeting_end)
})
itinerary.append({
    "action": "meet",
    "location": kenneth_location,
    "person": "Kenneth",
    "start_time": time_to_str(kenneth_meeting_start),
    "end_time": time_to_str(kenneth_meeting_end)
})

# The final output as a JSON-formatted dictionary.
output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))