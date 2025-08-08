#!/usr/bin/env python3
import json
import itertools

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define the travel times (in minutes) between locations.
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
    
    # Define friends' meeting constraints.
    # Times are stored in minutes since midnight.
    friends = {
        "Rebecca": {
            "location": "Bayview",
            "start": 9 * 60,             # 9:00
            "end": 12 * 60 + 45,         # 12:45
            "duration": 90
        },
        "Amanda": {
            "location": "Pacific Heights",
            "start": 18 * 60 + 30,       # 18:30
            "end": 21 * 60 + 45,         # 21:45
            "duration": 90
        },
        "James": {
            "location": "Alamo Square",
            "start": 9 * 60 + 45,        # 9:45
            "end": 21 * 60 + 15,         # 21:15
            "duration": 90
        },
        "Sarah": {
            "location": "Fisherman's Wharf",
            "start": 8 * 60,             # 8:00
            "end": 21 * 60 + 30,         # 21:30
            "duration": 90
        },
        "Melissa": {
            "location": "Golden Gate Park",
            "start": 9 * 60,             # 9:00
            "end": 18 * 60 + 45,         # 18:45
            "duration": 90
        }
    }
    
    # Starting at The Castro at 9:00AM.
    initial_time = 9 * 60  # 540 minutes
    initial_location = "The Castro"
    
    best_itinerary = []
    best_count = 0
    best_finish_time = float('inf')
    
    friend_names = list(friends.keys())
    
    # Evaluate all possible orders of meetings.
    for order in itertools.permutations(friend_names):
        current_time = initial_time
        current_location = initial_location
        itinerary = []
        feasible = True
        
        for friend in order:
            info = friends[friend]
            friend_location = info["location"]
            # Get travel time from current location to friend's location.
            travel = travel_times[current_location][friend_location]
            arrival_time = current_time + travel
            # Meeting can only start once the friend is available.
            meeting_start = max(arrival_time, info["start"])
            meeting_end = meeting_start + info["duration"]
            # Check if the meeting fits within the friend's available window.
            if meeting_end > info["end"]:
                feasible = False
                break
            # Append this meeting to the itinerary.
            itinerary.append({
                "action": "meet",
                "location": friend_location,
                "person": friend,
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            })
            # Update current time and location after meeting.
            current_time = meeting_end
            current_location = friend_location
        
        if feasible:
            meeting_count = len(itinerary)
            # Use finishing time as tiebreaker if needed.
            if meeting_count > best_count or (meeting_count == best_count and current_time < best_finish_time):
                best_count = meeting_count
                best_finish_time = current_time
                best_itinerary = itinerary

    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()