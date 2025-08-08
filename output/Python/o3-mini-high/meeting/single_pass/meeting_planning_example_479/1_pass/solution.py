#!/usr/bin/env python3
import itertools
import json

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def simulate_schedule(order, travel_times, start_time):
    current_time = start_time
    current_location = "Embarcadero"
    itinerary = []
    count = 0
    for friend in order:
        # Calculate travel time from current location to the friend's meeting location
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # The meeting cannot start before the friend's available start
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # If the meeting end exceeds the friend's available window, break out (cannot meet this friend)
        if meeting_end > friend["avail_end"]:
            break
        # Append the meeting details to the itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        count += 1
        current_time = meeting_end
        current_location = friend["location"]
    return count, current_time, itinerary

def main():
    # Define travel times in minutes between locations
    travel_times = {
        "Embarcadero": {
            "Golden Gate Park": 25,
            "Haight-Ashbury": 21,
            "Bayview": 21,
            "Presidio": 20,
            "Financial District": 5
        },
        "Golden Gate Park": {
            "Embarcadero": 25,
            "Haight-Ashbury": 7,
            "Bayview": 23,
            "Presidio": 11,
            "Financial District": 26
        },
        "Haight-Ashbury": {
            "Embarcadero": 20,
            "Golden Gate Park": 7,
            "Bayview": 18,
            "Presidio": 15,
            "Financial District": 21
        },
        "Bayview": {
            "Embarcadero": 19,
            "Golden Gate Park": 22,
            "Haight-Ashbury": 19,
            "Presidio": 31,
            "Financial District": 19
        },
        "Presidio": {
            "Embarcadero": 20,
            "Golden Gate Park": 12,
            "Haight-Ashbury": 15,
            "Bayview": 31,
            "Financial District": 23
        },
        "Financial District": {
            "Embarcadero": 4,
            "Golden Gate Park": 23,
            "Haight-Ashbury": 19,
            "Bayview": 19,
            "Presidio": 22
        }
    }

    # Friends with their meeting constraints.
    # Times are converted to minutes from midnight:
    # Mary: 8:45 (525) to 11:45 (705), min duration 45 minutes.
    # Kevin: 10:15 (615) to 16:15 (975), min duration 90 minutes.
    # Deborah: 15:00 (900) to 19:15 (1155), min duration 120 minutes.
    # Stephanie: 10:00 (600) to 17:15 (1035), min duration 120 minutes.
    # Emily: 11:30 (690) to 21:45 (1305), min duration 105 minutes.
    friends = [
        {"name": "Mary", "location": "Golden Gate Park", "avail_start": 8 * 60 + 45, "avail_end": 11 * 60 + 45, "duration": 45},
        {"name": "Kevin", "location": "Haight-Ashbury", "avail_start": 10 * 60 + 15, "avail_end": 16 * 60 + 15, "duration": 90},
        {"name": "Deborah", "location": "Bayview", "avail_start": 15 * 60, "avail_end": 19 * 60 + 15, "duration": 120},
        {"name": "Stephanie", "location": "Presidio", "avail_start": 10 * 60, "avail_end": 17 * 60 + 15, "duration": 120},
        {"name": "Emily", "location": "Financial District", "avail_start": 11 * 60 + 30, "avail_end": 21 * 60 + 45, "duration": 105}
    ]

    start_time = 9 * 60  # 9:00 AM in minutes
    best_itinerary = []
    best_count = 0
    best_finish_time = float('inf')

    # Try all possible orders of meeting friends and pick the itinerary with the most meetings.
    # If there is a tie, choose the one that finishes earliest.
    for order in itertools.permutations(friends):
        count, finish_time, itinerary = simulate_schedule(order, travel_times, start_time)
        if count > best_count or (count == best_count and finish_time < best_finish_time):
            best_count = count
            best_finish_time = finish_time
            best_itinerary = itinerary
        # Early exit if we managed to meet all friends
        if best_count == len(friends):
            continue

    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()