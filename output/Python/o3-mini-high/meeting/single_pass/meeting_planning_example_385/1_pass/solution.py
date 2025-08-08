#!/usr/bin/env python3
import json

# Define travel times between locations (in minutes)
travel_times = {
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Pacific Heights"): 11,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13
}

# Define friends' meeting constraints.
# Times are in minutes since midnight.
friends_data = {
    "Jeffrey": {
        "location": "Presidio",
        "avail_start": 8 * 60,         # 8:00
        "avail_end": 10 * 60,          # 10:00
        "duration": 105
    },
    "John": {
        "location": "Pacific Heights",
        "avail_start": 9 * 60,         # 9:00
        "avail_end": 13 * 60 + 30,     # 13:30
        "duration": 15
    },
    "Steven": {
        "location": "North Beach",
        "avail_start": 13 * 60 + 30,   # 13:30
        "avail_end": 22 * 60,          # 22:00
        "duration": 45
    },
    "Barbara": {
        "location": "Fisherman's Wharf",
        "avail_start": 18 * 60,        # 18:00
        "avail_end": 21 * 60 + 30,     # 21:30
        "duration": 30
    }
}

# Helper function to convert minutes since midnight to "H:MM" format.
def minutes_to_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Recursive search function.
# It returns a tuple: (count, finish_time, schedule)
# count: number of meetings scheduled,
# finish_time: time (in minutes) when the last meeting ends,
# schedule: list of meeting dictionaries for the itinerary.
def search(current_loc, current_time, remaining, current_schedule):
    # Start with the current schedule as the best candidate.
    best_count = len(current_schedule)
    best_finish = current_time
    best_sched = list(current_schedule)
    
    # Try scheduling each remaining friend.
    for friend in remaining:
        info = friends_data[friend]
        # Get travel time from current location to friend's location.
        travel = travel_times.get((current_loc, info["location"]))
        if travel is None:
            continue  # Skip if no travel info available.
        arrival_time = current_time + travel
        # Meeting can only start when both arrived and friend becomes available.
        meet_start = max(arrival_time, info["avail_start"])
        meet_end = meet_start + info["duration"]
        # Check if meeting fits within friend's availability window.
        if meet_end > info["avail_end"]:
            continue  # Not feasible to meet this friend.
        
        meeting = {
            "action": "meet",
            "location": info["location"],
            "person": friend,
            "start_time": minutes_to_str(meet_start),
            "end_time": minutes_to_str(meet_end)
        }
        new_schedule = current_schedule + [meeting]
        new_remaining = [f for f in remaining if f != friend]
        # Recurse from the friend's location and meeting end time.
        rec_count, rec_finish, rec_sched = search(info["location"], meet_end, new_remaining, new_schedule)
        
        # Compare with best solution found so far.
        if rec_count > best_count or (rec_count == best_count and rec_finish < best_finish):
            best_count = rec_count
            best_finish = rec_finish
            best_sched = rec_sched
    return best_count, best_finish, best_sched

def main():
    # Starting conditions: You arrive at Nob Hill at 9:00 (9*60 = 540 minutes).
    start_location = "Nob Hill"
    start_time = 9 * 60  # 9:00 in minutes
    # All friends are initially available to be scheduled.
    remaining = list(friends_data.keys())
    # Compute the optimal meeting schedule.
    _, _, optimal_schedule = search(start_location, start_time, remaining, [])
    # Prepare the result dictionary.
    result = {"itinerary": optimal_schedule}
    # Output the result as JSON.
    print(json.dumps(result))

if __name__ == "__main__":
    main()