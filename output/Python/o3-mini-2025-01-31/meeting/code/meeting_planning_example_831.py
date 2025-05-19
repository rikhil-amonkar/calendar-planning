#!/usr/bin/env python3
import json
from math import floor

# Helper functions to convert minutes since midnight to "H:MM" string (24-hr format)
def minutes_to_time(minutes):
    hrs = minutes // 60
    mins = minutes % 60
    return f"{hrs}:{mins:02d}"

# We use minutes since midnight for time arithmetic.
# Our starting time: 9:00AM = 9*60 = 540 minutes.
START_TIME = 9 * 60

# Travel times between locations (in minutes), given as a dictionary of dictionaries.
# Only the routes needed for our computed itinerary are defined.
# Our planned itinerary will visit:
# Presidio -> Fisherman's Wharf -> Alamo Square -> Financial District -> Embarcadero -> Golden Gate Park
travel_times = {
    "Presidio": {
        "Fisherman's Wharf": 19,
        "Alamo Square": 19,
        "Financial District": 23,
        "Embarcadero": 20,
        "Golden Gate Park": 12
    },
    "Fisherman's Wharf": {
        "Alamo Square": 21
    },
    "Alamo Square": {
        "Financial District": 17
    },
    "Financial District": {
        "Embarcadero": 4
    },
    "Embarcadero": {
        "Golden Gate Park": 25
    }
}

# Meeting constraints.
# Each friend is represented with:
#   person, location, available window (start, end in minutes since midnight),
#   minimum meeting duration (in minutes)
meetings = {
    "Jeffrey": {
        "location": "Fisherman's Wharf",
        "avail_start": 10 * 60 + 15,   # 10:15
        "avail_end": 13 * 60 + 0,        # 13:00
        "min_duration": 90
    },
    "Ronald": {
        "location": "Alamo Square",
        "avail_start": 7 * 60 + 45,      # 7:45
        "avail_end": 14 * 60 + 45,       # 14:45
        "min_duration": 120
    },
    "Jason": {
        "location": "Financial District",
        "avail_start": 10 * 60 + 45,     # 10:45
        "avail_end": 16 * 60 + 0,        # 16:00
        "min_duration": 105
    },
    "Margaret": {
        "location": "Embarcadero",
        "avail_start": 13 * 60 + 15,     # 13:15
        "avail_end": 19 * 60 + 0,        # 19:00
        "min_duration": 90
    },
    "George": {
        "location": "Golden Gate Park",
        "avail_start": 19 * 60 + 0,      # 19:00
        "avail_end": 22 * 60 + 0,        # 22:00
        "min_duration": 75
    }
}

# Our chosen order from our computed reasoning for a feasible schedule is:
# 1. Jeffrey at Fisherman's Wharf
# 2. Ronald at Alamo Square
# 3. Jason at Financial District
# 4. Margaret at Embarcadero
# 5. George at Golden Gate Park
#
# We compute the schedule by accumulating travel times and waiting if arrival is before person's available window.

itinerary = []

# Step 1: Start from Presidio, travel to Jeffrey's location.
current_time = START_TIME
# Travel: Presidio -> Fisherman's Wharf
current_time += travel_times["Presidio"]["Fisherman's Wharf"]
# If arrival is before Jeffrey's available start, wait until that time.
jeffrey = meetings["Jeffrey"]
if current_time < jeffrey["avail_start"]:
    current_time = jeffrey["avail_start"]
start_meeting = current_time
end_meeting = start_meeting + jeffrey["min_duration"]
# Ensure meeting ends within availability window (it does:  end_meeting <= avail_end)
if end_meeting > jeffrey["avail_end"]:
    raise ValueError("Cannot schedule Jeffrey meeting within his available window.")
itinerary.append({
    "action": "meet",
    "location": jeffrey["location"],
    "person": "Jeffrey",
    "start_time": minutes_to_time(start_meeting),
    "end_time": minutes_to_time(end_meeting)
})
current_time = end_meeting

# Step 2: Travel to Ronald's location (Alamo Square) from Fisherman's Wharf.
current_time += travel_times["Fisherman's Wharf"]["Alamo Square"]
ronald = meetings["Ronald"]
if current_time < ronald["avail_start"]:
    current_time = ronald["avail_start"]
start_meeting = current_time
end_meeting = start_meeting + ronald["min_duration"]
if end_meeting > ronald["avail_end"]:
    raise ValueError("Cannot schedule Ronald meeting within his available window.")
itinerary.append({
    "action": "meet",
    "location": ronald["location"],
    "person": "Ronald",
    "start_time": minutes_to_time(start_meeting),
    "end_time": minutes_to_time(end_meeting)
})
current_time = end_meeting

# Step 3: Travel to Jason's location (Financial District) from Alamo Square.
current_time += travel_times["Alamo Square"]["Financial District"]
jason = meetings["Jason"]
if current_time < jason["avail_start"]:
    current_time = jason["avail_start"]
start_meeting = current_time
end_meeting = start_meeting + jason["min_duration"]
if end_meeting > jason["avail_end"]:
    raise ValueError("Cannot schedule Jason meeting within his available window.")
itinerary.append({
    "action": "meet",
    "location": jason["location"],
    "person": "Jason",
    "start_time": minutes_to_time(start_meeting),
    "end_time": minutes_to_time(end_meeting)
})
current_time = end_meeting

# Step 4: Travel to Margaret's location (Embarcadero) from Financial District.
current_time += travel_times["Financial District"]["Embarcadero"]
margaret = meetings["Margaret"]
if current_time < margaret["avail_start"]:
    current_time = margaret["avail_start"]
start_meeting = current_time
end_meeting = start_meeting + margaret["min_duration"]
# We require the meeting to finish by avail_end.
if end_meeting > margaret["avail_end"]:
    # To adjust, we try to start at the latest possible time that still permits a full meeting.
    latest_start = margaret["avail_end"] - margaret["min_duration"]
    if latest_start < current_time:
        raise ValueError("Cannot schedule Margaret meeting within her available window.")
    start_meeting = latest_start
    end_meeting = start_meeting + margaret["min_duration"]
itinerary.append({
    "action": "meet",
    "location": margaret["location"],
    "person": "Margaret",
    "start_time": minutes_to_time(start_meeting),
    "end_time": minutes_to_time(end_meeting)
})
current_time = end_meeting

# Step 5: Travel to George's location (Golden Gate Park) from Embarcadero.
current_time += travel_times["Embarcadero"]["Golden Gate Park"]
george = meetings["George"]
if current_time < george["avail_start"]:
    current_time = george["avail_start"]
start_meeting = current_time
end_meeting = start_meeting + george["min_duration"]
if end_meeting > george["avail_end"]:
    raise ValueError("Cannot schedule George meeting within his available window.")
itinerary.append({
    "action": "meet",
    "location": george["location"],
    "person": "George",
    "start_time": minutes_to_time(start_meeting),
    "end_time": minutes_to_time(end_meeting)
})
current_time = end_meeting

# Build final result dictionary
result = {"itinerary": itinerary}

# Output the result as JSON.
print(json.dumps(result, indent=2))
                    
if __name__ == '__main__':
    pass