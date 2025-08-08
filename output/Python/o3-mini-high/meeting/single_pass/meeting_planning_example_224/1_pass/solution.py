#!/usr/bin/env python3
import json
import itertools

def minutes_to_time_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Define directed travel times between locations (in minutes)
    travel_times = {
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Richmond District"): 7,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Presidio"): 7
    }

    # Starting point: Arrive at Fisherman's Wharf at 9:00 AM
    start_time = 9 * 60  # minutes from midnight (9:00 AM = 540)
    start_location = "Fisherman's Wharf"

    # Define meeting constraints for each friend with availability windows and minimum meeting durations.
    friends = [
        {
            "name": "Melissa",
            "location": "Golden Gate Park",
            "avail_start": 8 * 60 + 30,  # 8:30 AM -> 510 minutes
            "avail_end": 20 * 60,        # 20:00 (8:00 PM) -> 1200 minutes
            "min_duration": 15
        },
        {
            "name": "Nancy",
            "location": "Presidio",
            "avail_start": 19 * 60 + 45, # 19:45 (7:45 PM) -> 1185 minutes
            "avail_end": 22 * 60,        # 22:00 (10:00 PM) -> 1320 minutes
            "min_duration": 105
        },
        {
            "name": "Emily",
            "location": "Richmond District",
            "avail_start": 16 * 60 + 45, # 16:45 (4:45 PM) -> 1005 minutes
            "avail_end": 22 * 60,        # 22:00 (10:00 PM) -> 1320 minutes
            "min_duration": 120
        }
    ]

    # We will try all permutations of meeting orders to maximize the number of friends met.
    best_itinerary = None
    best_count = 0
    best_finish_time = float('inf')

    for perm in itertools.permutations(friends):
        current_time = start_time
        current_location = start_location
        itinerary = []
        valid = True

        for friend in perm:
            # Get travel time from the current location to the friend's location.
            key = (current_location, friend["location"])
            if key not in travel_times:
                valid = False
                break
            travel_time = travel_times[key]
            arrival_time = current_time + travel_time

            # The meeting can only start once the friend is available.
            meeting_start = max(arrival_time, friend["avail_start"])
            meeting_end = meeting_start + friend["min_duration"]

            # Check if the meeting can be completed within the friend's availability window.
            if meeting_end > friend["avail_end"]:
                valid = False
                break

            # Add the meeting event to the itinerary.
            event = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            }
            itinerary.append(event)

            # Update the current time and location for the next meeting.
            current_time = meeting_end
            current_location = friend["location"]

        if valid:
            count = len(itinerary)
            # Choose the itinerary that meets the most friends.
            # If there is a tie, choose the one that finishes earlier.
            if count > best_count or (count == best_count and current_time < best_finish_time):
                best_count = count
                best_finish_time = current_time
                best_itinerary = itinerary

    # Prepare the final result dictionary.
    result = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()