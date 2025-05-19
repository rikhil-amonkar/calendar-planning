#!/usr/bin/env python3
import itertools
import json
from datetime import datetime, timedelta

def minutes_to_time_str(minutes):
    # Convert minutes from midnight to "H:MM" format (24-hour, no leading zero for hour)
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def simulate_schedule(order, start_time, start_location, travel_times, friends):
    itinerary = []
    current_time = start_time  # in minutes from midnight
    current_location = start_location
    for friend in order:
        # Get travel time from current_location to friend's location
        key = (current_location, friend["location"])
        if key not in travel_times:
            # if no direct route, schedule fails
            return None
        travel_time = travel_times[key]
        arrival_time = current_time + travel_time
        # Meeting can only start after friend available start time
        meeting_start = max(arrival_time, friend["available_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting fits in friend's available window
        if meeting_end > friend["available_end"]:
            return None
        # Append meeting event
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        })
        current_time = meeting_end
        current_location = friend["location"]
    return itinerary

def main():
    # Define travel times (in minutes)
    travel_times = {
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Embarcadero"): 8,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Embarcadero"): 9,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Embarcadero"): 19,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Mission District"): 20
    }
    
    # Define friends meeting info:
    # Times in minutes from midnight
    # Russian Hill arrival is at 9:00 => 9*60 = 540
    # Patricia: available from 18:30 (1110) to 21:45 (1305), duration 90 minutes, location "Nob Hill"
    # Ashley: available from 20:30 (1230) to 21:15 (1275), duration 45 minutes, location "Mission District"
    # Timothy: available from 9:45 (585) to 17:45 (1065), duration 120 minutes, location "Embarcadero"
    friends = [
        {
            "name": "Patricia",
            "location": "Nob Hill",
            "available_start": 18 * 60 + 30,  # 18:30 -> 1110 minutes
            "available_end": 21 * 60 + 45,      # 21:45 -> 1305 minutes
            "duration": 90
        },
        {
            "name": "Ashley",
            "location": "Mission District",
            "available_start": 20 * 60 + 30,  # 20:30 -> 1230 minutes
            "available_end": 21 * 60 + 15,      # 21:15 -> 1275 minutes
            "duration": 45
        },
        {
            "name": "Timothy",
            "location": "Embarcadero",
            "available_start": 9 * 60 + 45,    # 9:45 -> 585 minutes
            "available_end": 17 * 60 + 45,      # 17:45 -> 1065 minutes
            "duration": 120
        }
    ]
    
    # Starting conditions: Arrive at Russian Hill at 9:00AM (540 minutes)
    start_time = 9 * 60
    start_location = "Russian Hill"
    
    best_itinerary = None
    best_friend_count = 0

    # Check all permutations of friends (all meeting orders)
    for order in itertools.permutations(friends):
        itinerary = simulate_schedule(order, start_time, start_location, travel_times, order)
        if itinerary is not None:
            count = len(itinerary)
            if count > best_friend_count:
                best_friend_count = count
                best_itinerary = itinerary

    # If no full itinerary is found, best_itinerary might be None.
    # In our scenario, we expect to find the optimal meeting schedule meeting all three friends.
    output = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()