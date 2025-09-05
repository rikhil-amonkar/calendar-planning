import itertools
import json

def minutes_to_time_str(m):
    # Convert minutes since midnight to "H:MM" 24-hour format (hour with no leading zero, minutes always 2 digits)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define travel times in minutes between locations.
travel_times = {
    "The Castro": {
        "Bayview": 19,
        "Pacific Heights": 16,
        "Alamo Square": 8,
        "Fisherman's Wharf": 24,
        "Golden Gate Park": 11
    },
    "Bayview": {
        "The Castro": 20,
        "Pacific Heights": 23,
        "Alamo Square": 16,
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "The Castro": 16,
        "Bayview": 22,
        "Alamo Square": 10,
        "Fisherman's Wharf": 13,
        "Golden Gate Park": 15
    },
    "Alamo Square": {
        "The Castro": 8,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 9
    },
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Alamo Square": 20,
        "Golden Gate Park": 25
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Alamo Square": 10,
        "Fisherman's Wharf": 24
    }
}

# Define meeting constraints.
# Times are represented in minutes since midnight.
# 9:00 AM = 540 minutes.
start_time = 540  # 9:00 AM
meeting_duration = 90  # in minutes

# Each friend has a meeting location, an available time window, and a minimum meeting duration.
friends = [
    {
        "person": "Rebecca",
        "location": "Bayview",
        "avail_start": 540,    # 9:00 AM
        "avail_end": 765       # 12:45 PM (12*60 + 45)
    },
    {
        "person": "Amanda",
        "location": "Pacific Heights",
        "avail_start": 1110,   # 18:30 (6:30 PM)
        "avail_end": 1305      # 21:45 (9:45 PM)
    },
    {
        "person": "James",
        "location": "Alamo Square",
        "avail_start": 585,    # 9:45 AM
        "avail_end": 1275      # 21:15 (9:15 PM)
    },
    {
        "person": "Sarah",
        "location": "Fisherman's Wharf",
        "avail_start": 480,    # 8:00 AM
        "avail_end": 1290      # 21:30 (9:30 PM)
    },
    {
        "person": "Melissa",
        "location": "Golden Gate Park",
        "avail_start": 540,    # 9:00 AM
        "avail_end": 1125      # 18:45 (6:45 PM)
    }
]

# We'll use brute force to try every permutation of friend meetings.
best_itinerary = []
best_meetings_count = 0
best_finish_time = float('inf')

# Iterate over all possible orders.
for perm in itertools.permutations(friends):
    current_time = start_time
    current_location = "The Castro"
    itinerary = []
    meetings_count = 0
    valid = True
    # Process each meeting in the current permutation.
    for friend in perm:
        # Determine travel time from current location to friend's location.
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # Meeting can start only after arrival and not before friend’s available start.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + meeting_duration
        # Check if meeting fits within friend’s available window.
        if meeting_end > friend["avail_end"]:
            valid = False
            break
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["person"],
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        })
        meetings_count += 1
        current_time = meeting_end
        current_location = friend["location"]
    # We want to maximize the number of meetings. In case of a tie, choose the one finishing earlier.
    if meetings_count > best_meetings_count or (meetings_count == best_meetings_count and valid and current_time < best_finish_time):
        best_meetings_count = meetings_count
        best_finish_time = current_time
        best_itinerary = itinerary

# Prepare the result as specified.
result = {
    "itinerary": best_itinerary
}

# Output the result as a JSON-formatted string.
print(json.dumps(result, indent=2))