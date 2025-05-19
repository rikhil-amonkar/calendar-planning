#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

# Helper functions for time conversion
def str_to_minutes(time_str):
    # time_str in format "H:MM" (24-hour format)
    t = datetime.strptime(time_str, "%H:%M")
    return t.hour * 60 + t.minute

def minutes_to_str(minutes):
    # Converts minutes (since midnight) to "H:MM" format without leading zero in hour.
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Input parameters:
# Arrival time at Nob Hill
nob_hill_arrival = str_to_minutes("9:00")

# Meeting windows and minimum durations:
# Kenneth at Mission District: available 12:00 to 15:45, needs at least 45 minutes.
kenneth_available_start = str_to_minutes("12:00")
kenneth_available_end   = str_to_minutes("15:45")
kenneth_min_duration = 45

# Thomas at Pacific Heights: available 15:30 to 19:15, needs at least 75 minutes.
thomas_available_start = str_to_minutes("15:30")
thomas_available_end   = str_to_minutes("19:15")
thomas_min_duration = 75

# Travel times (in minutes) between locations:
travel_times = {
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Mission District"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Mission District"): 15,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Pacific Heights"): 16
}

# The goal is to meet as many friends as possible while respecting their availability windows
# and minimum meeting durations. We can attempt to use an algorithmic approach by exploring the logical options.
#
# One way to meet both friends is to visit Kenneth first at Mission District during his available window,
# then proceed to Pacific Heights to meet Thomas in his window.
#
# Steps:
# 1. Start at Nob Hill at 9:00.
# 2. Plan to reach Mission District exactly when Kenneth becomes available (12:00).
#    Compute departure time from Nob Hill: departure = Kenneth start time - travel time from Nob Hill to Mission District.
dep_time_nob_to_md = kenneth_available_start - travel_times[("Nob Hill", "Mission District")]
if dep_time_nob_to_md < nob_hill_arrival:
    # If the computed departure time is before arrival, wait until arrival.
    dep_time_nob_to_md = nob_hill_arrival

# Arrival at Mission District when meeting Kenneth.
kenneth_meet_start = kenneth_available_start
kenneth_meet_end = kenneth_meet_start + kenneth_min_duration
if kenneth_meet_end > kenneth_available_end:
    # If meeting cannot be accommodated in Kenneth's available window, then skip meeting.
    raise ValueError("Cannot schedule Kenneth meeting within his available time.")

# 3. After meeting Kenneth, travel from Mission District to Pacific Heights.
departure_md = kenneth_meet_end
arrival_ph = departure_md + travel_times[("Mission District", "Pacific Heights")]

# 4. Wait until Thomas is available at Pacific Heights. If arrival is earlier than his available start, schedule the meeting at his available start.
thomas_meet_start = max(arrival_ph, thomas_available_start)
thomas_meet_end = thomas_meet_start + thomas_min_duration
if thomas_meet_end > thomas_available_end:
    # If meeting Thomas cannot be accommodated, then skip his meeting.
    raise ValueError("Cannot schedule Thomas meeting within his available time.")

# Build itinerary as a list of meeting dictionaries; we include only meeting events.
itinerary = [
    {
        "action": "meet",
        "location": "Mission District",
        "person": "Kenneth",
        "start_time": minutes_to_str(kenneth_meet_start),
        "end_time": minutes_to_str(kenneth_meet_end)
    },
    {
        "action": "meet",
        "location": "Pacific Heights",
        "person": "Thomas",
        "start_time": minutes_to_str(thomas_meet_start),
        "end_time": minutes_to_str(thomas_meet_end)
    }
]

# Create the final schedule dictionary.
schedule = {"itinerary": itinerary}

# Output the result as JSON.
print(json.dumps(schedule, indent=2))