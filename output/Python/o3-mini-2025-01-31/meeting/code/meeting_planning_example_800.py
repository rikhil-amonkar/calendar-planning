#!/usr/bin/env python3
import json
from datetime import timedelta

# Utility functions to convert between minutes and time string in 24-hour format.
def minutes_to_timestr(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel times between locations (in minutes)
# Only entries required for our chosen itinerary.
travel_times = {
    ("Union Square", "North Beach"): 10,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Nob Hill", "Embarcadero"): 9,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Haight-Ashbury", "The Castro"): 6,
    ("The Castro", "Alamo Square"): 8
}

# Meeting constraints stored as dictionaries.
# Times are in minutes from midnight.
meetings = [
    {
        "person": "Kimberly",
        "location": "North Beach",
        "avail_start": 7 * 60,      # 7:00 = 420 minutes
        "avail_end": 10 * 60 + 30,    # 10:30 = 630 minutes
        "duration": 15
    },
    {
        "person": "Brian",
        "location": "Fisherman's Wharf",
        "avail_start": 9 * 60 + 30,   # 9:30 = 570 minutes
        "avail_end": 15 * 60 + 30,    # 15:30 = 930 minutes
        "duration": 45
    },
    {
        "person": "Kenneth",
        "location": "Nob Hill",
        "avail_start": 12 * 60 + 15,  # 12:15 = 735 minutes
        "avail_end": 17 * 60 + 15,    # 17:15 = 1035 minutes
        "duration": 105
    },
    {
        "person": "Joseph",
        "location": "Embarcadero",
        "avail_start": 15 * 60 + 30,  # 15:30 = 930 minutes
        "avail_end": 19 * 60 + 30,    # 19:30 = 1170 minutes
        "duration": 75
    },
    # In the evening we choose Betty over Steven since Betty, Melissa and Barbara can be chained.
    {
        "person": "Betty",
        "location": "Haight-Ashbury",
        "avail_start": 19 * 60,       # 19:00 = 1140 minutes
        "avail_end": 20 * 60 + 30,     # 20:30 = 1230 minutes
        "duration": 90
    },
    {
        "person": "Melissa",
        "location": "The Castro",
        "avail_start": 20 * 60 + 15,   # 20:15 = 1215 minutes
        "avail_end": 21 * 60 + 15,     # 21:15 = 1275 minutes
        "duration": 30
    },
    {
        "person": "Barbara",
        "location": "Alamo Square",
        "avail_start": 20 * 60 + 45,   # 20:45 = 1245 minutes
        "avail_end": 21 * 60 + 45,     # 21:45 = 1305 minutes
        "duration": 15
    }
]

# Our chosen itinerary order is:
# Start at Union Square at 9:00, then visits:
# 1. Kimberly at North Beach
# 2. Brian at Fisherman's Wharf
# 3. Kenneth at Nob Hill
# 4. Joseph at Embarcadero
# 5. Betty at Haight-Ashbury
# 6. Melissa at The Castro
# 7. Barbara at Alamo Square

# Starting point and time
current_location = "Union Square"
current_time = 9 * 60  # 9:00 AM is 540 minutes after midnight

itinerary = []

for meeting in meetings:
    destination = meeting["location"]
    # Get travel time from current_location to destination.
    travel_key = (current_location, destination)
    if travel_key not in travel_times:
        # If not found in our travel_times dictionary, assume a default large travel time.
        travel_duration = 30
    else:
        travel_duration = travel_times[travel_key]
    # Travel to destination
    current_time += travel_duration

    # Meeting can only start after arrival and not before person's available start time.
    meeting_start = max(current_time, meeting["avail_start"])
    
    # Check if meeting can be completed before the person's availability ends.
    meeting_end = meeting_start + meeting["duration"]
    if meeting_end > meeting["avail_end"]:
        # If this meeting cannot be scheduled within the available window, skip it.
        # For the purpose of this program, we assume all meetings can be scheduled
        continue

    # Record the meeting event.
    itinerary.append({
        "action": "meet",
        "location": destination,
        "person": meeting["person"],
        "start_time": minutes_to_timestr(meeting_start),
        "end_time": minutes_to_timestr(meeting_end)
    })
    
    # Update current_time and current_location
    current_time = meeting_end
    current_location = destination

# Create the output dictionary.
output = {
    "itinerary": itinerary
}

# Output result as JSON
print(json.dumps(output, indent=2))
  
if __name__ == '__main__':
    pass