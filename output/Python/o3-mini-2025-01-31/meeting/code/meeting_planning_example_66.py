#!/usr/bin/env python3
import json

def minutes_to_time_str(total_minutes):
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

# Input parameters (all times in minutes after midnight)
# Arrival at Nob Hill: 9:00AM -> 9 * 60 = 540 minutes
arrival_time_nob_hill = 9 * 60  # 540

# Robert's meeting availability at Presidio: 11:15AM to 17:45PM
robert_available_start = 11 * 60 + 15  # 675 minutes
robert_available_end = 17 * 60 + 45      # 1065 minutes

# Travel times in minutes
nobhill_to_presidio = 17
presidio_to_nobhill = 18

# Minimum meeting duration with Robert (in minutes)
min_meeting_duration = 120

# The plan is to meet Robert at Presidio.
# We need to leave Nob Hill with enough time such that we arrive at Presidio at or just at Robert's available start.
# Compute departure time from Nob Hill ensuring timely arrival at Robert's location.
# We want the meeting to start when Robert becomes available (or later if travel prevents it):
proposed_meeting_start = robert_available_start
# Calculate the departure time from Nob Hill needed to arrive by proposed_meeting_start:
departure_time_nob_hill = proposed_meeting_start - nobhill_to_presidio

# Ensure that we don't depart before we arrive at Nob Hill:
if departure_time_nob_hill < arrival_time_nob_hill:
    departure_time_nob_hill = arrival_time_nob_hill
    # Adjust meeting start accordingly
    proposed_meeting_start = departure_time_nob_hill + nobhill_to_presidio

# Determine meeting end time at Presidio
proposed_meeting_end = proposed_meeting_start + min_meeting_duration

# If the meeting end goes beyond Robert's available end time, adjust the meeting start (if possible)
if proposed_meeting_end > robert_available_end:
    # If there is slack, try shifting the meeting earlier.
    proposed_meeting_start = robert_available_end - min_meeting_duration
    # But we cannot start before Robert's available start.
    if proposed_meeting_start < robert_available_start:
        raise ValueError("Meeting cannot be scheduled to meet the minimum duration within Robert's available window.")
    proposed_meeting_end = proposed_meeting_start + min_meeting_duration

# Build itinerary JSON structure
itinerary = {
    "itinerary": [
        {
            "action": "meet",
            "location": "Presidio",
            "person": "Robert",
            "start_time": minutes_to_time_str(proposed_meeting_start),
            "end_time": minutes_to_time_str(proposed_meeting_end)
        }
    ]
}

# Print the JSON formatted itinerary
print(json.dumps(itinerary, indent=2))