#!/usr/bin/env python3
import json

# Function to convert minutes since midnight to a time string "H:MM" (24‐hour format)
def minutes_to_time(minutes):
    hrs = minutes // 60
    mins = minutes % 60
    return f"{hrs}:{mins:02d}"

# Travel times (in minutes) between locations
travel_times = {
    "Chinatown": {
        "Embarcadero": 5,
        "Pacific Heights": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 19,
        "Golden Gate Park": 23,
        "Fisherman's Wharf": 8,
        "Sunset District": 29,
        "The Castro": 22
    },
    "Embarcadero": {
        "Chinatown": 7,
        "Pacific Heights": 11,
        "Russian Hill": 8,
        "Haight-Ashbury": 21,
        "Golden Gate Park": 25,
        "Fisherman's Wharf": 6,
        "Sunset District": 30,
        "The Castro": 25
    },
    "Pacific Heights": {
        "Chinatown": 11,
        "Embarcadero": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Sunset District": 21,
        "The Castro": 16
    },
    "Russian Hill": {
        "Chinatown": 9,
        "Embarcadero": 8,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Golden Gate Park": 21,
        "Fisherman's Wharf": 7,
        "Sunset District": 23,
        "The Castro": 21
    },
    "Haight-Ashbury": {
        "Chinatown": 19,
        "Embarcadero": 20,
        "Pacific Heights": 12,
        "Russian Hill": 17,
        "Golden Gate Park": 7,
        "Fisherman's Wharf": 23,
        "Sunset District": 15,
        "The Castro": 6
    },
    "Golden Gate Park": {
        "Chinatown": 23,
        "Embarcadero": 25,
        "Pacific Heights": 16,
        "Russian Hill": 19,
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "Sunset District": 10,
        "The Castro": 13
    },
    "Fisherman's Wharf": {
        "Chinatown": 12,
        "Embarcadero": 8,
        "Pacific Heights": 12,
        "Russian Hill": 7,
        "Haight-Ashbury": 22,
        "Golden Gate Park": 25,
        "Sunset District": 27,
        "The Castro": 27
    },
    "Sunset District": {
        "Chinatown": 30,
        "Embarcadero": 30,
        "Pacific Heights": 21,
        "Russian Hill": 24,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "The Castro": 17
    },
    "The Castro": {
        "Chinatown": 22,
        "Embarcadero": 22,
        "Pacific Heights": 16,
        "Russian Hill": 18,
        "Haight-Ashbury": 6,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 24,
        "Sunset District": 17
    }
}

# Meeting constraints for each friend.
# Times are represented in minutes from midnight.
# 9:00 is 540 minutes.
# For each friend, we provide:
#   - location (where the meeting will take place)
#   - availability start time, availability end time (in minutes)
#   - minimum meeting duration (in minutes)
friends = [
    {"name": "Richard", "location": "Embarcadero", "avail_start": 15*60+15, "avail_end": 18*60+45, "duration": 90},
    {"name": "Mark", "location": "Pacific Heights", "avail_start": 15*60,     "avail_end": 17*60,     "duration": 45},
    {"name": "Matthew", "location": "Russian Hill",   "avail_start": 17*60+30, "avail_end": 21*60,     "duration": 90},
    {"name": "Rebecca", "location": "Haight-Ashbury", "avail_start": 14*60+45, "avail_end": 18*60,     "duration": 60},
    {"name": "Melissa", "location": "Golden Gate Park", "avail_start": 13*60+45, "avail_end": 17*60+30, "duration": 90},
    {"name": "Margaret", "location": "Fisherman's Wharf", "avail_start": 14*60+45, "avail_end": 20*60+15, "duration": 15},
    {"name": "Emily", "location": "Sunset District", "avail_start": 15*60+45, "avail_end": 17*60,     "duration": 45},
    {"name": "George", "location": "The Castro",     "avail_start": 14*60,    "avail_end": 16*60+15,  "duration": 75}
]

# DFS approach to search for the maximum (optimal) schedule.
# We want to maximize the number of meetings while satisfying travel and availability constraints.
def dfs(current_loc, current_time, remaining):
    best_schedule = []
    for i, friend in enumerate(remaining):
        # Calculate travel from current location to friend's location.
        travel = travel_times[current_loc][friend["location"]]
        arrival_time = current_time + travel
        # Meeting cannot start before the friend's availability starts.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if the meeting fits into the friend's available window.
        if meeting_end <= friend["avail_end"]:
            # Create a new list of remaining friends without the current one.
            new_remaining = remaining[:i] + remaining[i+1:]
            subsequent = dfs(friend["location"], meeting_end, new_remaining)
            candidate = [{
                "person": friend["name"],
                "location": friend["location"],
                "start": meeting_start,
                "end": meeting_end
            }] + subsequent
            if len(candidate) > len(best_schedule):
                best_schedule = candidate
    return best_schedule

def main():
    start_location = "Chinatown"
    start_time = 9 * 60  # 9:00 AM in minutes
    best = dfs(start_location, start_time, friends)
    
    # Build the itinerary in the required JSON format.
    itinerary = []
    for event in best:
        itinerary.append({
            "action": "meet",
            "location": event["location"],
            "person": event["person"],
            "start_time": minutes_to_time(event["start"]),
            "end_time": minutes_to_time(event["end"])
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()