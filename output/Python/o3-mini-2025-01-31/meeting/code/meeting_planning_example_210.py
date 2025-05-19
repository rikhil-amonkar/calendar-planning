#!/usr/bin/env python3
import json
from itertools import permutations

def minutes_to_timestr(minutes):
    """Convert minutes since midnight into H:MM 24-hour format without a leading zero on hours."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define starting point and start time (in minutes since midnight)
start_location = "Fisherman's Wharf"
start_time = 9 * 60  # 9:00 AM = 540 minutes

# Define friend meeting constraints: location, available start, available end, minimum meeting duration (all in minutes)
friends = {
    "Emily": {
        "location": "Presidio",
        "avail_start": 16 * 60 + 15,   # 16:15 -> 975 minutes
        "avail_end": 21 * 60,          # 21:00 -> 1260 minutes
        "min_duration": 105
    },
    "Joseph": {
        "location": "Richmond District",
        "avail_start": 17 * 60 + 15,   # 17:15 -> 1035 minutes
        "avail_end": 22 * 60,          # 22:00 -> 1320 minutes
        "min_duration": 120
    },
    "Melissa": {
        "location": "Financial District",
        "avail_start": 15 * 60 + 45,   # 15:45 -> 945 minutes
        "avail_end": 21 * 60 + 45,     # 21:45 -> 1305 minutes
        "min_duration": 75
    }
}

# Define travel times (in minutes) as a dictionary with keys (origin, destination)
travel_times = {
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Financial District"): 22,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Richmond District"): 21,
}

def get_travel_time(origin, destination):
    # if origin and destination are same return 0
    if origin == destination:
        return 0
    return travel_times.get((origin, destination), 9999)  # use high value if route missing

def compute_schedule(order):
    """
    Given an order which is a list of friend names, compute the meeting schedule.
    Returns a tuple (feasible, itinerary, end_time) where:
      feasible is True if schedule meets all constraints,
      itinerary is a list of meeting dictionaries,
      end_time is the finish time of the last meeting.
    """
    itinerary = []
    current_location = start_location
    current_time = start_time
    
    for friend in order:
        details = friends[friend]
        meeting_location = details["location"]
        # Travel from current_location to meeting_location
        travel = get_travel_time(current_location, meeting_location)
        arrival_time = current_time + travel
        # Wait if arrived before available start
        meeting_start = max(arrival_time, details["avail_start"])
        meeting_end = meeting_start + details["min_duration"]
        # Check if meeting_end is within friend's available window
        if meeting_end > details["avail_end"]:
            return (False, None, None)
        # Add the meeting event to itinerary
        itinerary.append({
            "action": "meet",
            "location": meeting_location,
            "person": friend,
            "start_time": minutes_to_timestr(meeting_start),
            "end_time": minutes_to_timestr(meeting_end)
        })
        # Update current time and location for next meeting
        current_time = meeting_end
        current_location = meeting_location
    return (True, itinerary, current_time)

def main():
    best_itinerary = None
    best_finish_time = None
    best_order = None
    # Try all permutations of the three friends
    friend_names = list(friends.keys())
    for order in permutations(friend_names):
        feasible, itinerary, finish_time = compute_schedule(order)
        if feasible:
            # Choose the schedule that finishes earliest
            if best_finish_time is None or finish_time < best_finish_time:
                best_finish_time = finish_time
                best_itinerary = itinerary
                best_order = order

    if best_itinerary is None:
        result = {"error": "No feasible meeting schedule found with the given constraints."}
    else:
        result = {"itinerary": best_itinerary}
    
    # Output the result as JSON-formatted dictionary
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()