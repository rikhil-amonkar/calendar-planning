#!/usr/bin/env python3
import json
from itertools import permutations

def minutes_to_time_str(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

# Input parameters
arrival_time = 9 * 60  # 9:00 AM = 540 minutes
start_location = "Embarcadero"

# Travel times (in minutes)
travel_times = {
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Alamo Square"): 19,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Alamo Square"): 17,
    ("Alamo Square", "Embarcadero"): 17,
    ("Alamo Square", "Financial District"): 17
}

# Friends' meeting constraints
friends = [
    {
        "person": "Stephanie",
        "location": "Financial District",
        "available_start": 8 * 60 + 15,  # 8:15 AM = 495 minutes
        "available_end": 11 * 60 + 30,     # 11:30 AM = 690 minutes
        "duration": 90
    },
    {
        "person": "John",
        "location": "Alamo Square",
        "available_start": 10 * 60 + 15,  # 10:15 AM = 615 minutes
        "available_end": 20 * 60 + 45,      # 20:45 = 1245 minutes
        "duration": 30
    }
]

# Function to compute a schedule for a given meeting order
def compute_schedule(order):
    schedule = []
    current_time = arrival_time
    current_location = start_location

    for friend in order:
        # Determine travel time from current_location to friend's location
        travel_key = (current_location, friend["location"])
        if travel_key not in travel_times:
            return None  # travel path undefined
        travel_time = travel_times[travel_key]
        arrival = current_time + travel_time
        
        # Meeting can only start when friend is available
        meeting_start = max(arrival, friend["available_start"])
        meeting_end = meeting_start + friend["duration"]
        
        # Check if meeting fits within friend's availability window
        if meeting_end > friend["available_end"]:
            return None
        
        schedule.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["person"],
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        })
        
        # Update current time and location for next meeting
        current_time = meeting_end
        current_location = friend["location"]

    return schedule

# Explore all meeting orders and select the one that meets the most friends
feasible_schedules = []
for order in permutations(friends, len(friends)):
    sched = compute_schedule(order)
    if sched is not None:
        feasible_schedules.append(sched)

# Choose the schedule that meets the maximum number of friends
best_schedule = max(feasible_schedules, key=len) if feasible_schedules else []

result = { "itinerary": best_schedule }

print(json.dumps(result, indent=2))