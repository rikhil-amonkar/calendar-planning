#!/usr/bin/env python3
import json
import itertools

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Start at Richmond District at 9:00 AM (540 minutes)
    start_time = 9 * 60
    start_location = "Richmond District"

    # Travel distances (in minutes) between locations
    travel_times = {
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Golden Gate Park"): 9,
        
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Mission District"): 24,
        ("Sunset District", "Golden Gate Park"): 11,
        
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Golden Gate Park"): 17,
        
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17,
    }

    # Define friends' meeting constraints and their locations
    # Times are in minutes since midnight.
    # Sarah: available 10:45 (645) to 19:00 (1140), meeting duration 30 minutes, at Sunset District.
    # Richard: available 11:45 (705) to 15:45 (945), meeting duration 90 minutes, at Haight-Ashbury.
    # Elizabeth: available 11:00 (660) to 17:15 (1035), meeting duration 120 minutes, at Mission District.
    # Michelle: available 18:15 (1095) to 20:45 (1245), meeting duration 90 minutes, at Golden Gate Park.
    friends = {
        "Sarah": {
            "location": "Sunset District",
            "avail_start": 10 * 60 + 45,  # 645
            "avail_end": 19 * 60,         # 1140
            "duration": 30,
        },
        "Richard": {
            "location": "Haight-Ashbury",
            "avail_start": 11 * 60 + 45,  # 705
            "avail_end": 15 * 60 + 45,    # 945
            "duration": 90,
        },
        "Elizabeth": {
            "location": "Mission District",
            "avail_start": 11 * 60,       # 660
            "avail_end": 17 * 60 + 15,    # 1035
            "duration": 120,
        },
        "Michelle": {
            "location": "Golden Gate Park",
            "avail_start": 18 * 60 + 15,  # 1095
            "avail_end": 20 * 60 + 45,    # 1245
            "duration": 90,
        }
    }

    friend_names = list(friends.keys())

    best_itinerary = []
    best_count = -1
    best_finish_time = float('inf')

    # Explore all orderings of friend meetings to maximize number of meetings
    for permutation in itertools.permutations(friend_names):
        current_time = start_time
        current_location = start_location
        itinerary = []
        count = 0
        feasible = True

        for person in permutation:
            friend = friends[person]
            location = friend["location"]
            travel = travel_times.get((current_location, location))
            if travel is None:
                feasible = False
                break
            arrival_time = current_time + travel
            # Start meeting when you arrive or when the friend becomes available (whichever is later)
            meeting_start = max(arrival_time, friend["avail_start"])
            meeting_end = meeting_start + friend["duration"]
            # If the meeting would end after the friend's availability, this ordering fails
            if meeting_end > friend["avail_end"]:
                feasible = False
                break

            # Append the meeting to the itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            # Update current location and time after finishing meeting
            current_time = meeting_end
            current_location = location
            count += 1

        # Choose the itinerary that meets the most friends; if tie, choose the one finishing earlier.
        if feasible and (count > best_count or (count == best_count and current_time < best_finish_time)):
            best_count = count
            best_finish_time = current_time
            best_itinerary = itinerary

    output = {"itinerary": best_itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()