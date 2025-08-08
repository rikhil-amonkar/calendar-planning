#!/usr/bin/env python3
import json

# Convert minutes since midnight to H:MM string (24-hour format)
def convert_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define the travel times (in minutes) between locations
travel_times = {
    "Financial District": {
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Union Square": 9,
        "Fisherman's Wharf": 10,
        "Pacific Heights": 13,
        "North Beach": 7
    },
    "Golden Gate Park": {
        "Financial District": 26,
        "Chinatown": 23,
        "Union Square": 22,
        "Fisherman's Wharf": 24,
        "Pacific Heights": 16,
        "North Beach": 24
    },
    "Chinatown": {
        "Financial District": 5,
        "Golden Gate Park": 23,
        "Union Square": 7,
        "Fisherman's Wharf": 8,
        "Pacific Heights": 10,
        "North Beach": 3
    },
    "Union Square": {
        "Financial District": 9,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Fisherman's Wharf": 15,
        "Pacific Heights": 15,
        "North Beach": 10
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Union Square": 13,
        "Pacific Heights": 12,
        "North Beach": 6
    },
    "Pacific Heights": {
        "Financial District": 13,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Union Square": 12,
        "Fisherman's Wharf": 13,
        "North Beach": 9
    },
    "North Beach": {
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Chinatown": 6,
        "Union Square": 7,
        "Fisherman's Wharf": 5,
        "Pacific Heights": 8
    }
}

# Define the meeting constraints for each friend.
# Times are expressed in minutes from midnight.
# For example, 9:00 AM = 9*60 = 540.
friends = [
    {
        "name": "Stephanie",
        "location": "Golden Gate Park",
        "avail_start": 11 * 60,         # 11:00 -> 660
        "avail_end": 15 * 60,           # 15:00 -> 900
        "duration": 105                 # minutes
    },
    {
        "name": "Karen",
        "location": "Chinatown",
        "avail_start": 13 * 60 + 45,    # 13:45 -> 825
        "avail_end": 16 * 60 + 30,      # 16:30 -> 990
        "duration": 15
    },
    {
        "name": "Brian",
        "location": "Union Square",
        "avail_start": 15 * 60,         # 15:00 -> 900
        "avail_end": 17 * 60 + 15,      # 17:15 -> 1035
        "duration": 30
    },
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "avail_start": 8 * 60,          # 8:00 -> 480
        "avail_end": 11 * 60 + 15,      # 11:15 -> 675
        "duration": 30
    },
    {
        "name": "Joseph",
        "location": "Pacific Heights",
        "avail_start": 8 * 60 + 15,     # 8:15 -> 495
        "avail_end": 9 * 60 + 30,       # 9:30 -> 570
        "duration": 60
    },
    {
        "name": "Steven",
        "location": "North Beach",
        "avail_start": 14 * 60 + 30,    # 14:30 -> 870
        "avail_end": 20 * 60 + 45,      # 20:45 -> 1245
        "duration": 120
    }
]

# Recursive backtracking search to find the optimal schedule.
# The function returns a tuple (itinerary, finish_time) where itinerary is a list
# of scheduled meeting events and finish_time is the end time of the last meeting.
def search(current_location, current_time, available_friends, itinerary):
    best_itinerary = itinerary
    best_finish_time = current_time
    best_count = len(itinerary)
    
    for i, friend in enumerate(available_friends):
        # Calculate travel time from current location to friend's location
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        
        # Determine when the meeting can start (must be within friend's available window)
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        
        # Check if the meeting can finish before the friend's availability ends
        if meeting_end <= friend["avail_end"]:
            event = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": convert_time(meeting_start),
                "end_time": convert_time(meeting_end)
            }
            new_itinerary = itinerary + [event]
            # Remove the friend from the list for subsequent meetings
            new_available = available_friends[:i] + available_friends[i+1:]
            candidate_itinerary, candidate_finish = search(friend["location"], meeting_end, new_available, new_itinerary)
            candidate_count = len(candidate_itinerary)
            
            # Choose the itinerary with more meetings; if equal, choose the one that finishes earlier.
            if candidate_count > best_count or (candidate_count == best_count and candidate_finish < best_finish_time):
                best_itinerary = candidate_itinerary
                best_finish_time = candidate_finish
                best_count = candidate_count
    return best_itinerary, best_finish_time

if __name__ == "__main__":
    # Start at Financial District at 9:00 AM (9*60 = 540 minutes)
    start_location = "Financial District"
    start_time = 9 * 60  # 540 minutes
    
    optimal_itinerary, finish_time = search(start_location, start_time, friends, [])
    
    result = {"itinerary": optimal_itinerary}
    print(json.dumps(result))