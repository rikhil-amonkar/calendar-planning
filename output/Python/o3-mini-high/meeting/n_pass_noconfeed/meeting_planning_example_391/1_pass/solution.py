import json
import itertools

def minutes_to_str(m):
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

def simulate_schedule(order, travel_times, start_time):
    current_time = start_time
    current_location = "Sunset District"
    itinerary = []
    for friend in order:
        # Calculate travel time from current location to friend's location
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # Wait if arrived before friend is available
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting can finish before the friend leaves
        if meeting_end > friend["avail_end"]:
            return None, None
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_str(meeting_start),
            "end_time": minutes_to_str(meeting_end)
        })
        current_time = meeting_end
        current_location = friend["location"]
    return current_time, itinerary

def main():
    # Define travel times (in minutes) between locations
    travel_times = {
        "Sunset District": {
            "Alamo Square": 17,
            "Russian Hill": 24,
            "Presidio": 16,
            "Financial District": 30
        },
        "Alamo Square": {
            "Sunset District": 16,
            "Russian Hill": 13,
            "Presidio": 18,
            "Financial District": 17
        },
        "Russian Hill": {
            "Sunset District": 23,
            "Alamo Square": 15,
            "Presidio": 14,
            "Financial District": 11
        },
        "Presidio": {
            "Sunset District": 15,
            "Alamo Square": 18,
            "Russian Hill": 14,
            "Financial District": 23
        },
        "Financial District": {
            "Sunset District": 31,
            "Alamo Square": 17,
            "Russian Hill": 10,
            "Presidio": 22
        }
    }
    
    # Meeting constraints for each friend:
    # Kevin: Available at Alamo Square from 8:15 to 21:30, minimum meeting duration = 75 minutes.
    # Kimberly: Available at Russian Hill from 8:45 to 12:30, minimum meeting duration = 30 minutes.
    # Joseph: Available at Presidio from 18:30 to 19:15, minimum meeting duration = 45 minutes.
    # Thomas: Available at Financial District from 19:00 to 21:45, minimum meeting duration = 45 minutes.
    #
    # Times are stored in minutes from midnight.
    friends = [
        {
            "name": "Kevin",
            "location": "Alamo Square",
            "avail_start": 8 * 60 + 15,   # 8:15 -> 495 minutes
            "avail_end": 21 * 60 + 30,    # 21:30 -> 1290 minutes
            "duration": 75
        },
        {
            "name": "Kimberly",
            "location": "Russian Hill",
            "avail_start": 8 * 60 + 45,   # 8:45 -> 525 minutes
            "avail_end": 12 * 60 + 30,    # 12:30 -> 750 minutes
            "duration": 30
        },
        {
            "name": "Joseph",
            "location": "Presidio",
            "avail_start": 18 * 60 + 30,  # 18:30 -> 1110 minutes
            "avail_end": 19 * 60 + 15,    # 19:15 -> 1155 minutes
            "duration": 45
        },
        {
            "name": "Thomas",
            "location": "Financial District",
            "avail_start": 19 * 60,       # 19:00 -> 1140 minutes
            "avail_end": 21 * 60 + 45,    # 21:45 -> 1305 minutes
            "duration": 45
        }
    ]
    
    # You arrive at Sunset District at 9:00 AM
    start_time = 9 * 60  # 9:00 -> 540 minutes

    best_itinerary = None
    best_finish_time = None
    best_meeting_count = 0

    # Try all permutations of meetings to maximize the friend count, and choose the one that finishes earliest.
    for permutation in itertools.permutations(friends):
        finish_time, itinerary = simulate_schedule(permutation, travel_times, start_time)
        if itinerary is None:
            continue
        meeting_count = len(itinerary)
        if (meeting_count > best_meeting_count or 
            (meeting_count == best_meeting_count and (best_finish_time is None or finish_time < best_finish_time))):
            best_meeting_count = meeting_count
            best_finish_time = finish_time
            best_itinerary = itinerary

    result = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(result))

if __name__ == "__main__":
    main()