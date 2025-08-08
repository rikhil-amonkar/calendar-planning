#!/usr/bin/env python3
import json
import itertools

# Helper function: convert minutes since midnight to H:MM format (24-hour, no leading zero for hour)
def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel times between locations (in minutes)
travel_times = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Fisherman's Wharf"): 29,
    
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Fisherman's Wharf"): 8,
    
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Fisherman's Wharf"): 19,
    
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Presidio"): 17
}

# Define participants with their constraints. Times are in minutes since midnight.
participants = [
    {
        "name": "William",
        "location": "Russian Hill",
        "avail_start": 18 * 60 + 30,  # 18:30 -> 1110
        "avail_end": 20 * 60 + 45,      # 20:45 -> 1245
        "min_meeting": 105
    },
    {
        "name": "Michelle",
        "location": "Chinatown",
        "avail_start": 8 * 60 + 15,     # 8:15 -> 495
        "avail_end": 14 * 60,           # 14:00 -> 840
        "min_meeting": 15
    },
    {
        "name": "George",
        "location": "Presidio",
        "avail_start": 10 * 60 + 30,    # 10:30 -> 630
        "avail_end": 18 * 60 + 45,      # 18:45 -> 1125
        "min_meeting": 30
    },
    {
        "name": "Robert",
        "location": "Fisherman's Wharf",
        "avail_start": 9 * 60,          # 9:00 -> 540
        "avail_end": 13 * 60 + 45,      # 13:45 -> 825
        "min_meeting": 30
    }
]

# Starting point and time: You arrive at Sunset District at 9:00AM.
start_location = "Sunset District"
start_time = 9 * 60  # 9:00 -> 540 minutes after midnight

# Function to simulate a schedule for a given ordering and return (feasible, itinerary, finish_time, count)
def simulate_schedule(ordering):
    current_time = start_time
    current_location = start_location
    itinerary = []
    
    for person in ordering:
        # Get travel time from current location to the participant's location
        travel_key = (current_location, person["location"])
        if travel_key not in travel_times:
            # If there's no defined travel time, skip this ordering as infeasible
            return False, [], float('inf'), 0
        travel_time = travel_times[travel_key]
        arrival_time = current_time + travel_time
        
        # Meeting must start not before the participant's available start time.
        meeting_start = max(arrival_time, person["avail_start"])
        meeting_end = meeting_start + person["min_meeting"]
        
        # Check if meeting fits within participant's available time window.
        if meeting_end > person["avail_end"]:
            return False, [], float('inf'), 0
        
        # Append this meeting to the itinerary.
        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        })
        
        # Update current time and location after finishing this meeting.
        current_time = meeting_end
        current_location = person["location"]
        
    return True, itinerary, current_time, len(itinerary)

# Try all permutations of the participants to find the optimal schedule.
best_itinerary = []
best_count = 0
best_finish_time = float('inf')

for ordering in itertools.permutations(participants):
    feasible, itinerary, finish_time, count = simulate_schedule(ordering)
    # We want to maximize meetings count, and then choose the one finishing earliest.
    if feasible:
        if count > best_count or (count == best_count and finish_time < best_finish_time):
            best_count = count
            best_finish_time = finish_time
            best_itinerary = itinerary

# Prepare the result as a JSON-formatted dictionary.
result = {"itinerary": best_itinerary}

# Output the JSON result.
print(json.dumps(result))