#!/usr/bin/env python3
import json
import itertools

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Define travel times in minutes between locations
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
    
    # Define each friend's meeting constraints (times in minutes from midnight)
    # Betty: available 19:45-21:45, needs at least 15 minutes; 
    # Karen: available 8:45-15:00, needs at least 30 minutes;
    # Anthony: available 9:15-21:30, needs at least 105 minutes.
    friends = [
        {
            "name": "Betty",
            "location": "Embarcadero",
            "avail_start": 19 * 60 + 45,  # 19:45 -> 1185 minutes
            "avail_end": 21 * 60 + 45,    # 21:45 -> 1305 minutes
            "duration": 15
        },
        {
            "name": "Karen",
            "location": "Fisherman's Wharf",
            "avail_start": 8 * 60 + 45,   # 8:45 -> 525 minutes
            "avail_end": 15 * 60,         # 15:00 -> 900 minutes
            "duration": 30
        },
        {
            "name": "Anthony",
            "location": "Financial District",
            "avail_start": 9 * 60 + 15,   # 9:15 -> 555 minutes
            "avail_end": 21 * 60 + 30,    # 21:30 -> 1290 minutes
            "duration": 105
        }
    ]
    
    # Starting location and time (Bayview at 9:00)
    start_location = "Bayview"
    start_time = 9 * 60  # 9:00 -> 540 minutes
    
    best_schedule = None
    best_finish_time = float('inf')
    
    # Check all possible orders (permutations) of meetings.
    for perm in itertools.permutations(friends):
        current_time = start_time
        current_location = start_location
        schedule = []
        feasible = True
        
        for friend in perm:
            # Determine travel time from current location to friend's location.
            key = (current_location, friend["location"])
            if key not in travel_times:
                feasible = False
                break
            travel = travel_times[key]
            arrival_time = current_time + travel
            # The meeting can only start once the friend is available.
            meeting_start = max(arrival_time, friend["avail_start"])
            meeting_end = meeting_start + friend["duration"]
            # Check if the meeting fits within the friend's availability window.
            if meeting_end > friend["avail_end"]:
                feasible = False
                break
            # Record the meeting event.
            schedule.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = friend["location"]
        
        # If the schedule is feasible, check if it finishes earlier.
        if feasible and current_time < best_finish_time:
            best_schedule = schedule
            best_finish_time = current_time
            
    result = {"itinerary": best_schedule if best_schedule is not None else []}
    print(json.dumps(result, indent=2))
    
if __name__ == '__main__':
    main()