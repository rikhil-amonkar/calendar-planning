#!/usr/bin/env python3
import json
from itertools import permutations

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def compute_schedule():
    # Define travel times (in minutes) between locations
    travel_times = {
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Alamo Square"): 19,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Alamo Square"): 17,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Financial District"): 17
    }
    
    # Define friends' meeting constraints and locations
    friends = {
        "Stephanie": {
            "location": "Financial District",
            "min_duration": 90,  # in minutes
            "available_start": 8 * 60 + 15,   # 8:15 AM -> 495 minutes
            "available_end": 11 * 60 + 30       # 11:30 AM -> 690 minutes
        },
        "John": {
            "location": "Alamo Square",
            "min_duration": 30,  # in minutes
            "available_start": 10 * 60 + 15,  # 10:15 AM -> 615 minutes
            "available_end": 20 * 60 + 45       # 20:45 -> 1245 minutes
        }
    }
    
    # Start at Embarcadero at 9:00 AM (540 minutes)
    initial_location = "Embarcadero"
    arrival_time = 9 * 60  # 540 minutes
    
    best_itinerary = []
    best_meetings_count = 0
    best_finish_time = float('inf')
    
    # Check all orders in which you could meet your friends
    for order in permutations(friends.keys(), len(friends)):
        itinerary = []
        current_location = initial_location
        current_time = arrival_time
        feasible = True
        
        for friend in order:
            friend_info = friends[friend]
            destination = friend_info["location"]
            
            # Ensure a travel time is defined from current_location to destination
            if (current_location, destination) not in travel_times:
                feasible = False
                break
                
            travel_time = travel_times[(current_location, destination)]
            arrival_at_destination = current_time + travel_time
            
            # The meeting starts when you arrive and when the friend is available
            meeting_start = max(arrival_at_destination, friend_info["available_start"])
            meeting_end = meeting_start + friend_info["min_duration"]
            
            # Check if the meeting can finish within your friend's availability window
            if meeting_end > friend_info["available_end"]:
                feasible = False
                break
            
            # Record the meeting event
            event = {
                "action": "meet",
                "location": destination,
                "person": friend,
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            }
            itinerary.append(event)
            
            # Update current location and time after meeting
            current_location = destination
            current_time = meeting_end
        
        if feasible:
            # Prefer itineraries that allow meeting more friends.
            # In case of ties, choose the one finishing earlier.
            if len(itinerary) > best_meetings_count or (len(itinerary) == best_meetings_count and current_time < best_finish_time):
                best_itinerary = itinerary
                best_meetings_count = len(itinerary)
                best_finish_time = current_time
                
    return {"itinerary": best_itinerary}

if __name__ == "__main__":
    schedule = compute_schedule()
    print(json.dumps(schedule, indent=2))