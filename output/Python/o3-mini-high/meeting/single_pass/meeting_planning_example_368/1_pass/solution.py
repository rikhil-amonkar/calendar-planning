#!/usr/bin/env python3
import json
import itertools

def time_to_minutes(t_str):
    parts = t_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define the travel times (in minutes) between locations
    travel_times = {
        "Bayview": {"Russian Hill": 23, "Alamo Square": 16, "North Beach": 21, "Financial District": 19},
        "Russian Hill": {"Bayview": 23, "Alamo Square": 15, "North Beach": 5, "Financial District": 11},
        "Alamo Square": {"Bayview": 16, "Russian Hill": 13, "North Beach": 15, "Financial District": 17},
        "North Beach": {"Bayview": 22, "Russian Hill": 4, "Alamo Square": 16, "Financial District": 8},
        "Financial District": {"Bayview": 19, "Russian Hill": 10, "Alamo Square": 17, "North Beach": 7}
    }
    
    # Define friends' meeting constraints
    friends = {
        "Joseph": {
            "location": "Russian Hill",
            "avail_start": time_to_minutes("8:30"),
            "avail_end": time_to_minutes("19:15"),
            "duration": 60
        },
        "Nancy": {
            "location": "Alamo Square",
            "avail_start": time_to_minutes("11:00"),
            "avail_end": time_to_minutes("16:00"),
            "duration": 90
        },
        "Jason": {
            "location": "North Beach",
            "avail_start": time_to_minutes("16:45"),
            "avail_end": time_to_minutes("21:45"),
            "duration": 15
        },
        "Jeffrey": {
            "location": "Financial District",
            "avail_start": time_to_minutes("10:30"),
            "avail_end": time_to_minutes("15:45"),
            "duration": 45
        }
    }
    
    # You arrive at Bayview at 9:00AM
    start_time = time_to_minutes("9:00")
    start_location = "Bayview"
    
    friend_names = list(friends.keys())
    
    best_schedule = []
    best_meeting_count = 0
    best_finish_time = float('inf')
    
    # Try all orderings of friends to maximize the number of meetings
    for perm in itertools.permutations(friend_names):
        current_time = start_time
        current_location = start_location
        itinerary = []
        feasible = True
        
        for friend in perm:
            friend_info = friends[friend]
            destination = friend_info["location"]
            
            # Compute travel time from current location to friend's location
            travel = travel_times[current_location][destination]
            arrival = current_time + travel
            
            # The meeting can only start once you arrive and when the friend is available
            meeting_start = max(arrival, friend_info["avail_start"])
            meeting_end = meeting_start + friend_info["duration"]
            
            # Check if the meeting can be completed within the friend's available window
            if meeting_end > friend_info["avail_end"]:
                feasible = False
                break
            
            itinerary.append({
                "action": "meet",
                "location": destination,
                "person": friend,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            
            # Update current time and location after the meeting
            current_time = meeting_end
            current_location = destination
        
        meeting_count = len(itinerary)
        # Choose the best schedule: maximum meetings, tie-break on finishing earlier
        if meeting_count > best_meeting_count or (meeting_count == best_meeting_count and current_time < best_finish_time):
            best_meeting_count = meeting_count
            best_finish_time = current_time
            best_schedule = itinerary

    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()