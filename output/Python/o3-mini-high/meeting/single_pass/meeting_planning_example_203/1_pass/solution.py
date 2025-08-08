#!/usr/bin/env python3
import json
import itertools

def minutes_to_timestr(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Input parameters
    # Travel distances in minutes between locations
    travel_times = {
        "Financial District": {
            "Fisherman's Wharf": 10,
            "Pacific Heights": 13,
            "Mission District": 17
        },
        "Fisherman's Wharf": {
            "Financial District": 11,
            "Pacific Heights": 12,
            "Mission District": 22
        },
        "Pacific Heights": {
            "Financial District": 13,
            "Fisherman's Wharf": 13,
            "Mission District": 15
        },
        "Mission District": {
            "Financial District": 17,
            "Fisherman's Wharf": 22,
            "Pacific Heights": 16
        }
    }

    # Meeting constraints for each friend.
    # Times are represented in minutes past midnight.
    # 9:00 is 540, 10:45 is 645, 12:15 is 735, 15:30 is 930, 19:45 is 1185.
    friends = [
        {
            "name": "David",
            "location": "Fisherman's Wharf",
            "avail_start": 645,   # 10:45
            "avail_end": 930,     # 15:30
            "duration": 15
        },
        {
            "name": "Timothy",
            "location": "Pacific Heights",
            "avail_start": 540,   # 9:00
            "avail_end": 930,     # 15:30
            "duration": 75
        },
        {
            "name": "Robert",
            "location": "Mission District",
            "avail_start": 735,   # 12:15
            "avail_end": 1185,    # 19:45
            "duration": 90
        }
    ]

    # Starting parameters: We start at Financial District at 9:00 (540 minutes)
    start_location = "Financial District"
    start_time = 540

    best_schedule = None
    best_finish_time = None

    # Try all permutations of the three meetings
    for perm in itertools.permutations(friends, len(friends)):
        current_time = start_time
        current_location = start_location
        itinerary = []
        feasible = True

        for friend in perm:
            # Calculate travel time from current location to friend's meeting location
            if current_location == friend["location"]:
                travel = 0
            else:
                travel = travel_times[current_location][friend["location"]]
            arrival_time = current_time + travel
            # Wait until the friend is available, if arriving too early
            meeting_start = max(arrival_time, friend["avail_start"])
            meeting_end = meeting_start + friend["duration"]
            # Check if meeting fits within the friend's available window
            if meeting_end > friend["avail_end"]:
                feasible = False
                break
            # Append meeting details to itinerary
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_timestr(meeting_start),
                "end_time": minutes_to_timestr(meeting_end)
            })
            # Update current time and location for next meeting
            current_time = meeting_end
            current_location = friend["location"]

        if feasible:
            # Use finish time as objective (minimize finish time)
            if best_finish_time is None or current_time < best_finish_time:
                best_finish_time = current_time
                best_schedule = itinerary

    # Prepare output structure
    result = {"itinerary": best_schedule if best_schedule is not None else []}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()