#!/usr/bin/env python3
import json
import itertools

def time_to_minutes(t):
    # Convert "H:MM" string to minutes since midnight.
    hours, minutes = t.split(":")
    return int(hours) * 60 + int(minutes)

def minutes_to_time(m):
    # Convert minutes since midnight back to "H:MM" string (24-hour format, no leading zero for hours)
    h = m // 60
    m_val = m % 60
    return f"{h}:{m_val:02d}"

# Define the travel times (in minutes) between locations.
travel_times = {
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "The Castro"): 19,
    
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "The Castro"): 13,
    
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,
    
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "The Castro"): 21,
    
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "The Castro"): 22,
    
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Chinatown"): 20
}

# Define each friend's meeting constraints.
friends = [
    {
        "name": "Andrew",
        "location": "Golden Gate Park",
        "avail_start": "11:45",  # Available from 11:45AM
        "avail_end": "14:30",    # Until 2:30PM
        "duration": 75           # Minimum meeting duration in minutes
    },
    {
        "name": "Sarah",
        "location": "Pacific Heights",
        "avail_start": "16:15",  # Available from 4:15PM
        "avail_end": "18:45",    # Until 6:45PM
        "duration": 15           # Minimum meeting duration in minutes
    },
    {
        "name": "Nancy",
        "location": "Presidio",
        "avail_start": "17:30",  # Available from 5:30PM
        "avail_end": "19:15",    # Until 7:15PM
        "duration": 60           # Minimum meeting duration in minutes
    },
    {
        "name": "Rebecca",
        "location": "Chinatown",
        "avail_start": "9:45",   # Available from 9:45AM
        "avail_end": "21:30",    # Until 9:30PM
        "duration": 90           # Minimum meeting duration in minutes
    },
    {
        "name": "Robert",
        "location": "The Castro",
        "avail_start": "8:30",   # Available from 8:30AM
        "avail_end": "14:15",    # Until 2:15PM
        "duration": 30           # Minimum meeting duration in minutes
    }
]

# Starting at Union Square at 9:00AM.
start_location = "Union Square"
start_time = time_to_minutes("9:00")

# We will explore all possible orders of meetings and choose the one that meets the maximum number of friends.
best_schedule = None
max_meetings = 0
best_end_time = float('inf')

# Iterate over all permutations (orders) of meetings.
for perm in itertools.permutations(friends):
    current_time = start_time
    current_location = start_location
    itinerary = []
    feasible = True
    for friend in perm:
        # Determine travel time from current location to the friend's location.
        travel = travel_times.get((current_location, friend["location"]))
        if travel is None:
            feasible = False
            break
        arrival = current_time + travel
        friend_avail_start = time_to_minutes(friend["avail_start"])
        friend_avail_end = time_to_minutes(friend["avail_end"])
        # The meeting can only start when the friend is available.
        meeting_start = max(arrival, friend_avail_start)
        meeting_end = meeting_start + friend["duration"]
        # Check if the meeting can be completed within the friend's available window.
        if meeting_end > friend_avail_end:
            feasible = False
            break
        # Append this meeting to our itinerary.
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = friend["location"]
    if feasible:
        if len(itinerary) > max_meetings or (len(itinerary) == max_meetings and current_time < best_end_time):
            best_schedule = itinerary
            max_meetings = len(itinerary)
            best_end_time = current_time

result = {"itinerary": best_schedule if best_schedule is not None else []}
print(json.dumps(result, indent=2))