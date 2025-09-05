#!/usr/bin/env python3
import itertools
import json

def time_to_minutes(t):
    # Convert time string "H:MM" into minutes since midnight.
    hours, minutes = t.split(':')
    return int(hours) * 60 + int(minutes)

def minutes_to_time(m):
    # Convert minutes since midnight into time string "H:MM" (24-hour format with no leading zero for hour)
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Starting parameters
    start_location = "Richmond District"
    start_time_str = "9:00"
    start_time = time_to_minutes(start_time_str)
    
    # Travel times in minutes between districts
    travel_times = {
        "Richmond District": {
            "Sunset District": 11,
            "Haight-Ashbury": 10,
            "Mission District": 20,
            "Golden Gate Park": 9
        },
        "Sunset District": {
            "Richmond District": 12,
            "Haight-Ashbury": 15,
            "Mission District": 24,
            "Golden Gate Park": 11
        },
        "Haight-Ashbury": {
            "Richmond District": 10,
            "Sunset District": 15,
            "Mission District": 11,
            "Golden Gate Park": 7
        },
        "Mission District": {
            "Richmond District": 20,
            "Sunset District": 24,
            "Haight-Ashbury": 12,
            "Golden Gate Park": 17
        },
        "Golden Gate Park": {
            "Richmond District": 7,
            "Sunset District": 10,
            "Haight-Ashbury": 7,
            "Mission District": 17
        }
    }
    
    # Define meeting constraints for each friend.
    meetings = [
        {
            "name": "Sarah",
            "location": "Sunset District",
            "available_start": "10:45",
            "available_end": "19:00",
            "duration": 30  # minutes
        },
        {
            "name": "Richard",
            "location": "Haight-Ashbury",
            "available_start": "11:45",
            "available_end": "15:45",
            "duration": 90  # minutes
        },
        {
            "name": "Elizabeth",
            "location": "Mission District",
            "available_start": "11:00",
            "available_end": "17:15",
            "duration": 120  # minutes
        },
        {
            "name": "Michelle",
            "location": "Golden Gate Park",
            "available_start": "18:15",
            "available_end": "20:45",
            "duration": 90  # minutes
        }
    ]
    
    # Precompute available start and end times in minutes for each meeting
    for m in meetings:
        m["avail_start_min"] = time_to_minutes(m["available_start"])
        m["avail_end_min"] = time_to_minutes(m["available_end"])
    
    best_schedule = None
    best_count = 0
    best_finish_time = float('inf')
    
    # Try all possible orders (permutations) of meeting friends.
    for perm in itertools.permutations(meetings):
        current_time = start_time
        current_location = start_location
        itinerary = []
        feasible = True
        
        for friend in perm:
            # Compute travel time from the current location to the friend's location.
            travel_time = travel_times[current_location][friend["location"]]
            arrival_time = current_time + travel_time
            
            # The meeting can only start when the friend is available.
            meeting_start = max(arrival_time, friend["avail_start_min"])
            meeting_end = meeting_start + friend["duration"]
            
            # Check if the meeting can be completed before the friend leaves.
            if meeting_end > friend["avail_end_min"]:
                feasible = False
                break
            
            # Append this meeting event to the itinerary.
            event = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            itinerary.append(event)
            
            # Update current time and location for the next meeting.
            current_time = meeting_end
            current_location = friend["location"]
        
        # If the schedule is feasible, update the best schedule if it meets more meetings
        # or finishes earlier (as a tiebreaker).
        if feasible:
            count = len(itinerary)
            if count > best_count or (count == best_count and current_time < best_finish_time):
                best_schedule = itinerary
                best_count = count
                best_finish_time = current_time
    
    # Prepare the final result in the required JSON structure.
    result = {"itinerary": best_schedule if best_schedule is not None else []}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    print("SOLUTION:")
    main()