#!/usr/bin/env python3
import json

def minutes_to_time_str(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define friends with their meeting constraints in minutes from midnight.
# Times: 9:00 = 540, 9:15 = 555, 10:45 = 645, 11:00 = 660, 13:00 = 780, etc.
friends = [
    {"person": "Matthew", "location": "Presidio", "avail_start": 11*60, "avail_end": 21*60, "duration": 90},
    {"person": "Margaret", "location": "Chinatown", "avail_start": 9*60+15, "avail_end": 18*60+45, "duration": 90},
    {"person": "Nancy", "location": "Pacific Heights", "avail_start": 14*60+15, "avail_end": 17*60, "duration": 15},
    {"person": "Helen", "location": "Richmond District", "avail_start": 19*60+45, "avail_end": 22*60, "duration": 60},
    {"person": "Rebecca", "location": "Fisherman's Wharf", "avail_start": 21*60+15, "avail_end": 22*60+15, "duration": 60},
    {"person": "Kimberly", "location": "Golden Gate Park", "avail_start": 13*60, "avail_end": 16*60+30, "duration": 120},
    {"person": "Kenneth", "location": "Bayview", "avail_start": 14*60+30, "avail_end": 18*60, "duration": 60}
]

# Travel times between locations in minutes.
travel_times = {
    "Russian Hill": {
        "Presidio": 14,
        "Chinatown": 9,
        "Pacific Heights": 7,
        "Richmond District": 14,
        "Fisherman's Wharf": 7,
        "Golden Gate Park": 21,
        "Bayview": 23,
        "Russian Hill": 0
    },
    "Presidio": {
        "Russian Hill": 14,
        "Chinatown": 21,
        "Pacific Heights": 11,
        "Richmond District": 7,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 12,
        "Bayview": 31,
        "Presidio": 0
    },
    "Chinatown": {
        "Russian Hill": 7,
        "Presidio": 19,
        "Pacific Heights": 10,
        "Richmond District": 20,
        "Fisherman's Wharf": 8,
        "Golden Gate Park": 23,
        "Bayview": 22,
        "Chinatown": 0
    },
    "Pacific Heights": {
        "Russian Hill": 7,
        "Presidio": 11,
        "Chinatown": 11,
        "Richmond District": 12,
        "Fisherman's Wharf": 13,
        "Golden Gate Park": 15,
        "Bayview": 22,
        "Pacific Heights": 0
    },
    "Richmond District": {
        "Russian Hill": 13,
        "Presidio": 7,
        "Chinatown": 20,
        "Pacific Heights": 10,
        "Fisherman's Wharf": 18,
        "Golden Gate Park": 9,
        "Bayview": 26,
        "Richmond District": 0
    },
    "Fisherman's Wharf": {
        "Russian Hill": 7,
        "Presidio": 17,
        "Chinatown": 12,
        "Pacific Heights": 12,
        "Richmond District": 18,
        "Golden Gate Park": 25,
        "Bayview": 26,
        "Fisherman's Wharf": 0
    },
    "Golden Gate Park": {
        "Russian Hill": 19,
        "Presidio": 11,
        "Chinatown": 23,
        "Pacific Heights": 16,
        "Richmond District": 7,
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Golden Gate Park": 0
    },
    "Bayview": {
        "Russian Hill": 23,
        "Presidio": 31,
        "Chinatown": 18,
        "Pacific Heights": 23,
        "Richmond District": 25,
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22,
        "Bayview": 0
    }
}

# Recursive search function that returns the optimal meeting chain (maximizing number of meetings)
def search(current_location, current_time, remaining):
    best_schedule = []
    for i, f in enumerate(remaining):
        # Compute travel time to the friend's location
        travel_time = travel_times[current_location][f["location"]]
        arrival_time = current_time + travel_time
        # Meeting can only start when both you and the friend are available.
        start_meeting = max(arrival_time, f["avail_start"])
        end_meeting = start_meeting + f["duration"]
        if end_meeting <= f["avail_end"]:
            meeting = {
                "person": f["person"],
                "location": f["location"],
                "start": start_meeting,
                "end": end_meeting
            }
            # Exclude the current friend and search further.
            new_remaining = remaining[:i] + remaining[i+1:]
            next_schedule = search(f["location"], end_meeting, new_remaining)
            candidate_schedule = [meeting] + next_schedule
            if len(candidate_schedule) > len(best_schedule):
                best_schedule = candidate_schedule
    return best_schedule

def main():
    start_location = "Russian Hill"
    start_time = 9 * 60  # 9:00 AM in minutes (540 minutes)
    optimal_schedule = search(start_location, start_time, friends)
    
    itinerary = []
    for meeting in optimal_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time_str(meeting["start"]),
            "end_time": minutes_to_time_str(meeting["end"])
        })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()