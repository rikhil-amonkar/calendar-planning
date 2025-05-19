#!/usr/bin/env python3
import itertools
import json

def time_to_minutes(time_str):
    """Converts a time string H:MM (24-hour) to minutes since midnight."""
    parts = time_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    """Converts minutes since midnight to H:MM (24-hour) format (no leading zero for hour)."""
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel times (in minutes)
travel_times = {
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Bayview"): 26,
    
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Bayview"): 15,
    
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Mission District"): 13
}

# Define meeting constraints for each friend.
# Times are stored in minutes since midnight.
meetings = [
    {
        "person": "Sarah",
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("14:45"),
        "avail_end": time_to_minutes("17:30"),
        "duration": 105
    },
    {
        "person": "Mary",
        "location": "Richmond District",
        "avail_start": time_to_minutes("13:00"),
        "avail_end": time_to_minutes("19:15"),
        "duration": 75
    },
    {
        "person": "Helen",
        "location": "Mission District",
        "avail_start": time_to_minutes("21:45"),
        "avail_end": time_to_minutes("22:30"),
        "duration": 30
    },
    {
        "person": "Thomas",
        "location": "Bayview",
        "avail_start": time_to_minutes("15:15"),
        "avail_end": time_to_minutes("18:45"),
        "duration": 120
    },
]

# Starting conditions
start_location = "Haight-Ashbury"
start_time = time_to_minutes("9:00")

def get_travel_time(origin, destination):
    # Look up travel time for the specific route
    return travel_times.get((origin, destination), None)

def evaluate_schedule(order):
    """
    Given an order (permutation) of meetings (list of dicts),
    compute the itinerary if feasible.
    Returns tuple: (number_of_meetings, finish_time, itinerary) 
    where itinerary is a list of steps.
    If a meeting cannot be scheduled due to availability constraints, 
    we skip scheduling further meetings in this order.
    """
    itinerary = []
    curr_location = start_location
    curr_time = start_time

    count = 0
    # We'll try to schedule meetings in the order given.
    for meet in order:
        travel = get_travel_time(curr_location, meet["location"])
        if travel is None:
            # If route not available, schedule fails.
            return (count, curr_time, itinerary)
        # Travel and update current time
        curr_time += travel
        # If arrival is before the meeting availability start, wait.
        if curr_time < meet["avail_start"]:
            curr_time = meet["avail_start"]
        # Check if meeting can be held before the availability end.
        if curr_time + meet["duration"] > meet["avail_end"]:
            # Cannot schedule this meeting fully - break out.
            return (count, curr_time, itinerary)
        meet_start = curr_time
        meet_end = curr_time + meet["duration"]
        # Add the meeting to itinerary (convert times to H:MM)
        itinerary.append({
            "action": "meet",
            "location": meet["location"],
            "person": meet["person"],
            "start_time": minutes_to_time(meet_start),
            "end_time": minutes_to_time(meet_end)
        })
        # Update current time and location
        curr_time = meet_end
        curr_location = meet["location"]
        count += 1
    return (count, curr_time, itinerary)

def main():
    best_itinerary = None
    best_count = -1
    best_finish_time = None

    # We'll consider all possible orders (permutations) of the meetings.
    for order in itertools.permutations(meetings):
        count, finish_time, itinerary = evaluate_schedule(order)
        # Choose the schedule with the maximum count.
        # In case of tie, choose the one with the earliest finish time.
        if count > best_count or (count == best_count and (best_finish_time is None or finish_time < best_finish_time)):
            best_count = count
            best_finish_time = finish_time
            best_itinerary = itinerary

    # Our goal is to meet as many friends as possible.
    # If not all meetings can be scheduled, best_itinerary reflects the maximum count.
    output = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()