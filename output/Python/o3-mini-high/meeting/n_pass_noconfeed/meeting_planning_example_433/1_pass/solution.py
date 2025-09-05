import itertools
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Travel times (in minutes) between locations
    travel = {
        "Nob Hill": {
            "Richmond District": 14,
            "Financial District": 9,
            "North Beach": 8,
            "The Castro": 17,
            "Golden Gate Park": 17
        },
        "Richmond District": {
            "Nob Hill": 17,
            "Financial District": 22,
            "North Beach": 17,
            "The Castro": 16,
            "Golden Gate Park": 9
        },
        "Financial District": {
            "Nob Hill": 8,
            "Richmond District": 21,
            "North Beach": 7,
            "The Castro": 23,
            "Golden Gate Park": 23
        },
        "North Beach": {
            "Nob Hill": 7,
            "Richmond District": 18,
            "Financial District": 8,
            "The Castro": 22,
            "Golden Gate Park": 22
        },
        "The Castro": {
            "Nob Hill": 16,
            "Richmond District": 16,
            "Financial District": 20,
            "North Beach": 20,
            "Golden Gate Park": 11
        },
        "Golden Gate Park": {
            "Nob Hill": 20,
            "Richmond District": 7,
            "Financial District": 26,
            "North Beach": 24,
            "The Castro": 13
        }
    }

    # Meeting constraints for each friend (times in minutes from midnight)
    # Emily: 19:00 to 21:00, min 15 minutes
    # Margaret: 16:30 to 20:15, min 75 minutes
    # Ronald: 18:30 to 19:30, min 45 minutes
    # Deborah: 13:45 to 21:15, min 90 minutes
    # Jeffrey: 11:15 to 14:30, min 120 minutes
    friends = [
        {"name": "Emily", "location": "Richmond District", "avail_start": 19*60, "avail_end": 21*60, "min_duration": 15},
        {"name": "Margaret", "location": "Financial District", "avail_start": 16*60 + 30, "avail_end": 20*60 + 15, "min_duration": 75},
        {"name": "Ronald", "location": "North Beach", "avail_start": 18*60 + 30, "avail_end": 19*60 + 30, "min_duration": 45},
        {"name": "Deborah", "location": "The Castro", "avail_start": 13*60 + 45, "avail_end": 21*60 + 15, "min_duration": 90},
        {"name": "Jeffrey", "location": "Golden Gate Park", "avail_start": 11*60 + 15, "avail_end": 14*60 + 30, "min_duration": 120},
    ]

    # Starting at Nob Hill at 9:00AM (9*60 minutes)
    start_location = "Nob Hill"
    start_time = 9 * 60

    best_itinerary = None
    best_count = -1
    best_end_time = float('inf')

    # Try all orders in which to meet friends
    for perm in itertools.permutations(friends):
        current_time = start_time
        current_location = start_location
        itinerary = []
        feasible = True
        for friend in perm:
            # Determine travel time from current location to friend's location
            if current_location not in travel or friend["location"] not in travel[current_location]:
                feasible = False
                break
            travel_time = travel[current_location][friend["location"]]
            arrival_time = current_time + travel_time
            # Wait until friend is available if arriving early
            meeting_start = max(arrival_time, friend["avail_start"])
            meeting_end = meeting_start + friend["min_duration"]
            if meeting_end > friend["avail_end"]:
                feasible = False
                break
            meeting_info = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            itinerary.append(meeting_info)
            current_time = meeting_end
            current_location = friend["location"]
        if feasible:
            count = len(itinerary)
            # Choose the itinerary with most meetings; tie-breaker: earliest finish time
            if count > best_count or (count == best_count and current_time < best_end_time):
                best_count = count
                best_itinerary = itinerary
                best_end_time = current_time

    result = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()