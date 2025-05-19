#!/usr/bin/env python3
import json
import itertools

def time_to_minutes(time_str):
    # time_str format: "H:MM" in 24-hour format
    parts = time_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_timestr(minutes):
    hour = minutes // 60
    minute = minutes % 60
    # Using no leading zero for hour, but ensuring minute is two-digit if needed.
    return f"{hour}:{minute:02d}"

# Input parameters
start_time_str = "9:00"  # Arrival at Richmond District
start_location = "Richmond District"
start_time = time_to_minutes(start_time_str)

# Friends meeting constraints
friends = [
    {
        "name": "Sarah",
        "location": "Sunset District",
        "avail_start": time_to_minutes("10:45"),
        "avail_end": time_to_minutes("19:00"),
        "min_duration": 30
    },
    {
        "name": "Richard",
        "location": "Haight-Ashbury",
        "avail_start": time_to_minutes("11:45"),
        "avail_end": time_to_minutes("15:45"),
        "min_duration": 90
    },
    {
        "name": "Elizabeth",
        "location": "Mission District",
        "avail_start": time_to_minutes("11:00"),
        "avail_end": time_to_minutes("17:15"),
        "min_duration": 120
    },
    {
        "name": "Michelle",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("18:15"),
        "avail_end": time_to_minutes("20:45"),
        "min_duration": 90
    }
]

# Travel times (in minutes) as a dictionary with (from, to) tuples
travel_times = {
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Golden Gate Park"): 17,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
}

# Function to simulate meeting schedule for a given order of friend visits.
def simulate_schedule(order):
    current_time = start_time
    current_location = start_location
    itinerary = []
    
    for friend in order:
        # Determine travel time from current location to friend's location
        travel_key = (current_location, friend["location"])
        # In case there is no direct key (should be present as per input), we assume not feasible.
        if travel_key not in travel_times:
            return None, None
        travel_time = travel_times[travel_key]
        arrival_time = current_time + travel_time
        
        # Meeting can only start when friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_duration"]
        
        # Check if meeting can finish before friend leaves.
        if meeting_end > friend["avail_end"]:
            return None, None
        
        # Add meeting details to itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_timestr(meeting_start),
            "end_time": minutes_to_timestr(meeting_end)
        })
        
        # Update current time and location for next travel.
        current_time = meeting_end
        current_location = friend["location"]
    
    return itinerary, current_time

# We want to maximize the number of friends met.
# We'll try all permutations of the friends list.
best_itinerary = None
best_count = 0
best_finish_time = None

for order in itertools.permutations(friends):
    schedule, finish_time = simulate_schedule(order)
    if schedule is not None:
        meeting_count = len(schedule)
        # We prefer schedules that do more meetings, and tie-breaker: earlier finish time.
        if meeting_count > best_count or (meeting_count == best_count and (best_finish_time is None or finish_time < best_finish_time)):
            best_itinerary = schedule
            best_count = meeting_count
            best_finish_time = finish_time

# If no full schedule is feasible with all meetings, best_itinerary might be None.
# For this problem, the computed schedule order should be feasible.
if best_itinerary is None:
    result = {"itinerary": []}
else:
    result = {"itinerary": best_itinerary}

# Output result as JSON-formatted dictionary.
print(json.dumps(result, indent=2))