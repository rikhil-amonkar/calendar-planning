#!/usr/bin/env python3
import json
import itertools

# Helper functions
def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Data: travel times (in minutes) between locations.
# Locations: Presidio, Richmond District, North Beach, Financial District, Golden Gate Park, Union Square
travel_times = {
    "Presidio": {
        "Richmond District": 7,
        "North Beach": 18,
        "Financial District": 23,
        "Golden Gate Park": 12,
        "Union Square": 22
    },
    "Richmond District": {
        "Presidio": 7,
        "North Beach": 17,
        "Financial District": 22,
        "Golden Gate Park": 9,
        "Union Square": 21
    },
    "North Beach": {
        "Presidio": 17,
        "Richmond District": 18,
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Union Square": 7
    },
    "Financial District": {
        "Presidio": 22,
        "Richmond District": 21,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Union Square": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Richmond District": 7,
        "North Beach": 24,
        "Financial District": 26,
        "Union Square": 22
    },
    "Union Square": {
        "Presidio": 24,
        "Richmond District": 20,
        "North Beach": 10,
        "Financial District": 9,
        "Golden Gate Park": 22
    }
}

# Friend meeting constraints and details.
friends = [
    {
        "name": "Jason",
        "location": "Richmond District",
        "avail_start": 13 * 60,         # 13:00 = 780
        "avail_end": 20 * 60 + 45,        # 20:45 = 1245
        "min_meeting": 90
    },
    {
        "name": "Melissa",
        "location": "North Beach",
        "avail_start": 18 * 60 + 45,      # 18:45 = 1125
        "avail_end": 20 * 60 + 15,        # 20:15 = 1215
        "min_meeting": 45
    },
    {
        "name": "Brian",
        "location": "Financial District",
        "avail_start": 9 * 60 + 45,       # 9:45 = 585
        "avail_end": 21 * 60 + 45,        # 21:45 = 1305
        "min_meeting": 15
    },
    {
        "name": "Elizabeth",
        "location": "Golden Gate Park",
        "avail_start": 8 * 60 + 45,       # 8:45 = 525
        "avail_end": 21 * 60 + 30,        # 21:30 = 1290
        "min_meeting": 105
    },
    {
        "name": "Laura",
        "location": "Union Square",
        "avail_start": 14 * 60 + 15,      # 14:15 = 855
        "avail_end": 19 * 60 + 30,        # 19:30 = 1170
        "min_meeting": 75
    }
]

# Start location and time
start_location = "Presidio"
start_time = 9 * 60  # 9:00 AM is 540 minutes

def compute_schedule(order):
    """Given an order of meetings (list of friend dicts), compute timeline if feasible.
       Returns itinerary (list) and finish_time if feasible; otherwise returns None."""
    itinerary = []
    current_time = start_time
    current_location = start_location
    total_wait = 0  # total waiting minutes (not required for output, but could choose best schedule)
    
    for friend in order:
        # Travel from current location to friend's location
        if current_location == friend["location"]:
            travel = 0
        else:
            travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        
        # Meeting start time is the later of arrival and friend's available start
        meeting_start = max(arrival_time, friend["avail_start"])
        wait_time = meeting_start - arrival_time
        total_wait += wait_time
        
        meeting_end = meeting_start + friend["min_meeting"]
        
        # Check if meeting fits in friend's available window
        if meeting_end > friend["avail_end"]:
            return None
        
        # Append meeting to itinerary (times converted to string)
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        })
        
        # Update current_time and current_location for next meeting.
        current_time = meeting_end
        current_location = friend["location"]
    return {
        "itinerary": itinerary,
        "finish_time": current_time,
        "total_wait": total_wait
    }

def main():
    best_schedule = None
    best_finish_time = None
    best_wait = None
    best_order = None
    
    # Iterate over all permutations of the friends
    for perm in itertools.permutations(friends):
        schedule = compute_schedule(perm)
        if schedule is not None:
            # Since we want to meet as many friends as possible, feasible schedule with all 5
            # Between multiple feasible schedules, we pick one with minimal finish time, then minimal waiting time.
            if best_schedule is None:
                best_schedule = schedule
                best_finish_time = schedule["finish_time"]
                best_wait = schedule["total_wait"]
                best_order = perm
            else:
                if schedule["finish_time"] < best_finish_time:
                    best_schedule = schedule
                    best_finish_time = schedule["finish_time"]
                    best_wait = schedule["total_wait"]
                    best_order = perm
                elif schedule["finish_time"] == best_finish_time and schedule["total_wait"] < best_wait:
                    best_schedule = schedule
                    best_finish_time = schedule["finish_time"]
                    best_wait = schedule["total_wait"]
                    best_order = perm

    if best_schedule is None:
        # If no schedule is possible for all friends, output an empty itinerary.
        result = {"itinerary": []}
    else:
        # Only output the itinerary portion.
        result = {"itinerary": best_schedule["itinerary"]}
    print(json.dumps(result, indent=2))
    
if __name__ == '__main__':
    main()