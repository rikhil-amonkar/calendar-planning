#!/usr/bin/env python3
import itertools
import json

def format_time(t):
    # t is in minutes since midnight
    hours = t // 60
    minutes = t % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times in minutes (not necessarily symmetric)
    travel_times = {
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Union Square"): 22,

        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Union Square"): 21,

        ("North Beach", "Presidio"): 17,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Union Square"): 7,

        ("Financial District", "Presidio"): 22,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Union Square"): 9,

        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Union Square"): 22,

        ("Union Square", "Presidio"): 24,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Golden Gate Park"): 22,
    }

    # Define friends with their meeting constraints.
    # Times are stored in minutes since midnight.
    friends = [
        {
            "name": "Jason",
            "location": "Richmond District",
            "avail_start": 13 * 60,               # 13:00 -> 780
            "avail_end": 20 * 60 + 45,              # 20:45 -> 1245
            "duration": 90
        },
        {
            "name": "Melissa",
            "location": "North Beach",
            "avail_start": 18 * 60 + 45,            # 18:45 -> 1125
            "avail_end": 20 * 60 + 15,              # 20:15 -> 1215
            "duration": 45
        },
        {
            "name": "Brian",
            "location": "Financial District",
            "avail_start": 9 * 60 + 45,             # 9:45 -> 585
            "avail_end": 21 * 60 + 45,              # 21:45 -> 1305
            "duration": 15
        },
        {
            "name": "Elizabeth",
            "location": "Golden Gate Park",
            "avail_start": 8 * 60 + 45,             # 8:45 -> 525
            "avail_end": 21 * 60 + 30,              # 21:30 -> 1290
            "duration": 105
        },
        {
            "name": "Laura",
            "location": "Union Square",
            "avail_start": 14 * 60 + 15,            # 14:15 -> 855
            "avail_end": 19 * 60 + 30,              # 19:30 -> 1170
            "duration": 75
        },
    ]

    # You start your day at the Presidio at 9:00 (540 minutes since midnight)
    start_location = "Presidio"
    start_time = 9 * 60  # 9:00 -> 540

    best_schedule = []
    best_count = -1
    best_total_wait = float('inf')

    # Try every permutation of friend meetings.
    for perm in itertools.permutations(friends):
        current_time = start_time
        current_location = start_location
        itinerary = []
        total_wait = 0
        count = 0
        feasible = True
        for person in perm:
            # Determine travel time to friend's location.
            key = (current_location, person["location"])
            if key not in travel_times:
                feasible = False
                break
            travel = travel_times[key]
            arrival_time = current_time + travel
            meeting_start = max(arrival_time, person["avail_start"])
            wait = meeting_start - arrival_time
            meeting_end = meeting_start + person["duration"]
            # Check if the meeting finishes before the friend leaves.
            if meeting_end > person["avail_end"]:
                feasible = False
                break
            # Record this meeting in the itinerary.
            itinerary.append({
                "action": "meet",
                "location": person["location"],
                "person": person["name"],
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
            total_wait += wait
            current_time = meeting_end
            current_location = person["location"]
            count += 1
        if feasible:
            # Our primary goal is to maximize the number of friends met.
            # If tied, we choose the schedule with less waiting time.
            if count > best_count or (count == best_count and total_wait < best_total_wait):
                best_schedule = itinerary
                best_count = count
                best_total_wait = total_wait

    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()