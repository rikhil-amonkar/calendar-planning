#!/usr/bin/env python3
import json

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel times (in minutes) between locations.
travel_times = {
    "Golden Gate Park": {
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Mission District": 17,
        "Embarcadero": 25,
        "Financial District": 26
    },
    "Fisherman's Wharf": {
        "Golden Gate Park": 25,
        "Bayview": 26,
        "Mission District": 22,
        "Embarcadero": 8,
        "Financial District": 11
    },
    "Bayview": {
        "Golden Gate Park": 22,
        "Fisherman's Wharf": 25,
        "Mission District": 13,
        "Embarcadero": 19,
        "Financial District": 19
    },
    "Mission District": {
        "Golden Gate Park": 17,
        "Fisherman's Wharf": 22,
        "Bayview": 15,
        "Embarcadero": 19,
        "Financial District": 17
    },
    "Embarcadero": {
        "Golden Gate Park": 25,
        "Fisherman's Wharf": 6,
        "Bayview": 21,
        "Mission District": 20,
        "Financial District": 5
    },
    "Financial District": {
        "Golden Gate Park": 23,
        "Fisherman's Wharf": 10,
        "Bayview": 19,
        "Mission District": 17,
        "Embarcadero": 4
    }
}

# Define friend meeting constraints.
# Times are in minutes from midnight.
# Joseph: available 8:00 (480) to 17:30 (1050), meeting duration min 90.
# Jeffrey: available 17:30 (1050) to 21:30 (1290), meeting duration min 60.
# Kevin: available 11:15 (675) to 15:15 (915), meeting duration min 30.
# David: available 8:15 (495) to 9:00 (540), meeting duration min 30.
# Barbara: available 10:30 (630) to 16:30 (990), meeting duration min 15.
friends = [
    {"name": "Joseph", "location": "Fisherman's Wharf", "avail_start": 480, "avail_end": 1050, "min_duration": 90},
    {"name": "Jeffrey", "location": "Bayview", "avail_start": 1050, "avail_end": 1290, "min_duration": 60},
    {"name": "Kevin", "location": "Mission District", "avail_start": 675, "avail_end": 915, "min_duration": 30},
    {"name": "David", "location": "Embarcadero", "avail_start": 495, "avail_end": 540, "min_duration": 30},
    {"name": "Barbara", "location": "Financial District", "avail_start": 630, "avail_end": 990, "min_duration": 15}
]

# Recursive depth-first search to build a schedule that meets the constraints.
def dfs(current_location, current_time, remaining, schedule):
    best_schedule = schedule
    for i, friend in enumerate(remaining):
        # If travel time from current location to friend's location is defined.
        if current_location not in travel_times or friend["location"] not in travel_times[current_location]:
            continue
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        # The meeting can only start when both you arrive and the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        # Check if there is enough time to have the minimum meeting before the friend leaves.
        if meeting_start + friend["min_duration"] <= friend["avail_end"]:
            meeting_end = meeting_start + friend["min_duration"]
            meeting = {
                "person": friend["name"],
                "location": friend["location"],
                "start": meeting_start,
                "end": meeting_end
            }
            new_schedule = schedule + [meeting]
            new_remaining = remaining[:i] + remaining[i+1:]
            candidate_schedule = dfs(friend["location"], meeting_end, new_remaining, new_schedule)
            if len(candidate_schedule) > len(best_schedule):
                best_schedule = candidate_schedule
    return best_schedule

def main():
    # You arrive at Golden Gate Park at 9:00 AM (9*60 = 540 minutes).
    start_location = "Golden Gate Park"
    start_time = 540
    best = dfs(start_location, start_time, friends, [])

    # Format the computed schedule as the required JSON structure.
    itinerary = []
    for meeting in best:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time_str(meeting["start"]),
            "end_time": minutes_to_time_str(meeting["end"])
        })

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()