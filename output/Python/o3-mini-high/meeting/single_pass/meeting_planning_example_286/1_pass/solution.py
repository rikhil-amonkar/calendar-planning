#!/usr/bin/env python3
import itertools
import json

def minutes_to_time_string(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def simulate_schedule(order, travel_times, start_time):
    itinerary = []
    current_time = start_time
    current_location = "Union Square"
    
    for friend in order:
        # Get travel time from current_location to the friend's location
        if friend["location"] not in travel_times[current_location]:
            return None
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # The meeting can only start once the friend is available
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        if meeting_end > friend["avail_end"]:
            return None
        # Add the meeting event to the itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time_string(meeting_start),
            "end_time": minutes_to_time_string(meeting_end)
        })
        current_time = meeting_end
        current_location = friend["location"]
    return itinerary, current_time

def main():
    # Define travel distances (in minutes) between locations
    travel_times = {
        "Union Square": {
            "Mission District": 14,
            "Bayview": 15,
            "Sunset District": 26
        },
        "Mission District": {
            "Union Square": 15,
            "Bayview": 15,
            "Sunset District": 24
        },
        "Bayview": {
            "Union Square": 17,
            "Mission District": 13,
            "Sunset District": 23
        },
        "Sunset District": {
            "Union Square": 30,
            "Mission District": 24,
            "Bayview": 22
        }
    }
    
    # Define meeting constraints for each friend (times in minutes since midnight)
    friends = [
        {
            "name": "Carol",
            "location": "Sunset District",
            "avail_start": 10 * 60 + 15,  # 10:15
            "avail_end": 11 * 60 + 45,    # 11:45
            "duration": 30
        },
        {
            "name": "Karen",
            "location": "Bayview",
            "avail_start": 12 * 60 + 45,  # 12:45
            "avail_end": 15 * 60,         # 15:00
            "duration": 120
        },
        {
            "name": "Rebecca",
            "location": "Mission District",
            "avail_start": 11 * 60 + 30,  # 11:30
            "avail_end": 20 * 60 + 15,    # 20:15
            "duration": 120
        }
    ]
    
    start_time = 9 * 60  # 9:00 in minutes since midnight
    
    best_itinerary = None
    best_meetings = 0
    best_finish_time = float('inf')
    
    # Try all orders of meeting friends to maximize how many meetings can be scheduled
    for order in itertools.permutations(friends):
        result = simulate_schedule(order, travel_times, start_time)
        if result is None:
            continue
        itinerary, finish_time = result
        meeting_count = len(itinerary)
        # Prioritize more meetings; if tied, choose the one that finishes earlier
        if meeting_count > best_meetings or (meeting_count == best_meetings and finish_time < best_finish_time):
            best_meetings = meeting_count
            best_finish_time = finish_time
            best_itinerary = itinerary

    output = {"itinerary": best_itinerary if best_itinerary else []}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()