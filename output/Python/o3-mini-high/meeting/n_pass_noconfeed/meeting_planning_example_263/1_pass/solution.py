import json

def minutes_to_timestr(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel times in minutes between locations (origin, destination)
travel_times = {
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Financial District"): 19,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Financial District"): 5,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Fisherman's Wharf"): 10
}

# Meeting constraints for each friend.
# Times are stored as minutes past midnight.
meetings = {
    "Betty": {
        "location": "Embarcadero",
        "avail_start": 19 * 60 + 45,  # 19:45 -> 1185 minutes
        "avail_end": 21 * 60 + 45,    # 21:45 -> 1305 minutes
        "min_duration": 15
    },
    "Karen": {
        "location": "Fisherman's Wharf",
        "avail_start": 8 * 60 + 45,   # 8:45 -> 525 minutes
        "avail_end": 15 * 60,         # 15:00 -> 900 minutes
        "min_duration": 30
    },
    "Anthony": {
        "location": "Financial District",
        "avail_start": 9 * 60 + 15,   # 9:15 -> 555 minutes
        "avail_end": 21 * 60 + 30,    # 21:30 -> 1290 minutes
        "min_duration": 105
    }
}

# Starting point: arriving at Bayview at 9:00 AM.
start_location = "Bayview"
start_time = 9 * 60  # 9:00 AM -> 540 minutes

# We plan an itinerary that visits:
#   1. Karen at Fisherman's Wharf
#   2. Anthony at Financial District
#   3. Betty at Embarcadero
# The schedule is computed backward from Betty's availability.

# Schedule Betty's meeting at the earliest time she is available.
betty_start = meetings["Betty"]["avail_start"]  # 19:45 (1185 minutes)
betty_end = betty_start + meetings["Betty"]["min_duration"]  # Must meet at least 15 mins (1200 minutes -> 20:00)

# For a seamless connection, Anthony’s meeting must finish in time to travel to Betty’s location.
# Travel time from Financial District to Embarcadero:
fd_to_eb = travel_times[("Financial District", "Embarcadero")]
anthony_end = betty_start - fd_to_eb  # 1185 - 4 = 1181 minutes (i.e. 19:41)
anthony_start = anthony_end - meetings["Anthony"]["min_duration"]  # 1181 - 105 = 1076 minutes

# For Karen, we choose the latest possible slot within her availability.
# The latest she can finish (and still be available) is 15:00 (900 minutes).
karen_end = meetings["Karen"]["avail_end"]  # 900 minutes (15:00)
karen_start = karen_end - meetings["Karen"]["min_duration"]  # 900 - 30 = 870 minutes (14:30)

# Check travel feasibility from starting point to Karen's meeting.
# Need to depart Bayview so as to arrive at Fisherman's Wharf by 14:30.
bayview_to_fw = travel_times[(start_location, "Fisherman's Wharf")]
depart_bayview = karen_start - bayview_to_fw  # 870 - 25 = 845 minutes (14:05)
assert depart_bayview >= start_time, "Insufficient time to travel from start location to first meeting."

# After Karen meeting ends at 15:00, travel from Fisherman's Wharf to Financial District
fw_to_fd = travel_times[(meetings["Karen"]["location"], "Financial District")]
arrival_fd = karen_end + fw_to_fd  # 900 + 11 = 911 minutes
# This arrival time is before Anthony's meeting start (1076 minutes) so waiting at FD is needed.

# Construct the itinerary with computed meeting times.
itinerary = [
    {
        "action": "meet",
        "location": meetings["Karen"]["location"],
        "person": "Karen",
        "start_time": minutes_to_timestr(karen_start),
        "end_time": minutes_to_timestr(karen_end)
    },
    {
        "action": "meet",
        "location": meetings["Anthony"]["location"],
        "person": "Anthony",
        "start_time": minutes_to_timestr(anthony_start),
        "end_time": minutes_to_timestr(anthony_end)
    },
    {
        "action": "meet",
        "location": meetings["Betty"]["location"],
        "person": "Betty",
        "start_time": minutes_to_timestr(betty_start),
        "end_time": minutes_to_timestr(betty_end)
    }
]

output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))