#!/usr/bin/env python3
import json
import itertools

def minutes_to_time_str(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

def simulate_schedule(order, travel_times, start_time, start_loc):
    current_time = start_time
    current_loc = start_loc
    itinerary = []
    for friend in order:
        # Travel from current location to friend's location
        travel = travel_times.get((current_loc, friend["location"]))
        if travel is None:
            return None
        current_time += travel  # arrival time at friend's location
        # Wait until friend is available, if needed
        meeting_start = max(current_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting fits in the friend's availability window
        if meeting_end > friend["avail_end"]:
            return None
        # Record the meeting in the itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        })
        # Update current time and location for the next meeting
        current_time = meeting_end
        current_loc = friend["location"]
    return (len(order), current_time, itinerary)

def main():
    # Start at The Castro at 9:00AM (9*60 = 540 minutes after midnight)
    start_time = 9 * 60
    start_loc = "The Castro"

    # Define travel times (in minutes) between locations
    travel_times = {
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Chinatown"): 20,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Chinatown"): 16,
        ("Union Square", "The Castro"): 19,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Union Square"): 7,
    }

    # Define friends and their meeting constraints
    # Times are in minutes after midnight.
    # Emily is at Alamo Square from 11:45 (705) to 15:15 (915) and needs 105 minutes.
    # Barbara is at Union Square from 16:45 (1005) to 18:15 (1095) and needs 60 minutes.
    # William is at Chinatown from 17:15 (1035) to 19:00 (1140) and needs 105 minutes.
    friends = [
        {
            "name": "Emily",
            "location": "Alamo Square",
            "avail_start": 11 * 60 + 45,  # 11:45 AM -> 705 minutes
            "avail_end": 15 * 60 + 15,    # 15:15 -> 915 minutes
            "duration": 105
        },
        {
            "name": "Barbara",
            "location": "Union Square",
            "avail_start": 16 * 60 + 45,  # 16:45 -> 1005 minutes
            "avail_end": 18 * 60 + 15,    # 18:15 -> 1095 minutes
            "duration": 60
        },
        {
            "name": "William",
            "location": "Chinatown",
            "avail_start": 17 * 60 + 15,  # 17:15 -> 1035 minutes
            "avail_end": 19 * 60,         # 19:00 -> 1140 minutes
            "duration": 105
        }
    ]

    best_schedule = None
    best_count = 0
    best_finish_time = float("inf")
    
    # Try all non-empty subsets and all orders (permutations) of friends.
    for r in range(1, len(friends)+1):
        for subset in itertools.combinations(friends, r):
            for order in itertools.permutations(subset):
                result = simulate_schedule(order, travel_times, start_time, start_loc)
                if result is not None:
                    count, finish_time, itinerary = result
                    # We want to maximize the number of friends met.
                    # In case of a tie, choose the schedule that finishes earlier.
                    if count > best_count or (count == best_count and finish_time < best_finish_time):
                        best_count = count
                        best_finish_time = finish_time
                        best_schedule = itinerary

    # Output the optimal itinerary as a JSON-formatted dictionary.
    output = {"itinerary": best_schedule if best_schedule is not None else []}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()