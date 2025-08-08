#!/usr/bin/env python3
import json
import copy

# Convert time in minutes (since midnight) to "H:MM" string (24-hour, no leading zero on hour)
def minutes_to_timestr(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times dictionary (in minutes)
travel_times = {
    "Union Square": {
        "Mission District": 14,
        "Fisherman's Wharf": 15,
        "Russian Hill": 13,
        "Marina District": 18,
        "North Beach": 10,
        "Chinatown": 7,
        "Pacific Heights": 15,
        "The Castro": 17,
        "Nob Hill": 9,
        "Sunset District": 27
    },
    "Mission District": {
        "Union Square": 15,
        "Fisherman's Wharf": 22,
        "Russian Hill": 15,
        "Marina District": 19,
        "North Beach": 17,
        "Chinatown": 16,
        "Pacific Heights": 16,
        "The Castro": 7,
        "Nob Hill": 12,
        "Sunset District": 24
    },
    "Fisherman's Wharf": {
        "Union Square": 13,
        "Mission District": 22,
        "Russian Hill": 7,
        "Marina District": 9,
        "North Beach": 6,
        "Chinatown": 12,
        "Pacific Heights": 12,
        "The Castro": 27,
        "Nob Hill": 11,
        "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10,
        "Mission District": 16,
        "Fisherman's Wharf": 7,
        "Marina District": 7,
        "North Beach": 5,
        "Chinatown": 9,
        "Pacific Heights": 7,
        "The Castro": 21,
        "Nob Hill": 5,
        "Sunset District": 23
    },
    "Marina District": {
        "Union Square": 16,
        "Mission District": 20,
        "Fisherman's Wharf": 10,
        "Russian Hill": 8,
        "North Beach": 11,
        "Chinatown": 15,
        "Pacific Heights": 7,
        "The Castro": 22,
        "Nob Hill": 12,
        "Sunset District": 19
    },
    "North Beach": {
        "Union Square": 7,
        "Mission District": 18,
        "Fisherman's Wharf": 5,
        "Russian Hill": 4,
        "Marina District": 9,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 23,
        "Nob Hill": 7,
        "Sunset District": 27
    },
    "Chinatown": {
        "Union Square": 7,
        "Mission District": 17,
        "Fisherman's Wharf": 8,
        "Russian Hill": 7,
        "Marina District": 12,
        "North Beach": 3,
        "Pacific Heights": 10,
        "The Castro": 22,
        "Nob Hill": 9,
        "Sunset District": 29
    },
    "Pacific Heights": {
        "Union Square": 12,
        "Mission District": 15,
        "Fisherman's Wharf": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "North Beach": 9,
        "Chinatown": 11,
        "The Castro": 16,
        "Nob Hill": 8,
        "Sunset District": 21
    },
    "The Castro": {
        "Union Square": 19,
        "Mission District": 7,
        "Fisherman's Wharf": 24,
        "Russian Hill": 18,
        "Marina District": 21,
        "North Beach": 20,
        "Chinatown": 22,
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Sunset District": 17
    },
    "Nob Hill": {
        "Union Square": 7,
        "Mission District": 13,
        "Fisherman's Wharf": 10,
        "Russian Hill": 5,
        "Marina District": 11,
        "North Beach": 8,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 17,
        "Sunset District": 24
    },
    "Sunset District": {
        "Union Square": 30,
        "Mission District": 25,
        "Fisherman's Wharf": 29,
        "Russian Hill": 24,
        "Marina District": 21,
        "North Beach": 28,
        "Chinatown": 30,
        "Pacific Heights": 21,
        "The Castro": 17,
        "Nob Hill": 27
    }
}

# Meeting constraints for friends.
# Times are in minutes after midnight.
# Note: 9:00 is 540, 13:00 is 780, 15:00 is 900, 17:15 is 1035, 20:00 is 1200, etc.
friends = [
    {"person": "Kevin", "location": "Mission District", "avail_start": 20 * 60 + 45, "avail_end": 21 * 60 + 45, "duration": 60},   # 1245-1305
    {"person": "Mark", "location": "Fisherman's Wharf", "avail_start": 17 * 60 + 15, "avail_end": 20 * 60, "duration": 90},         # 1035-1200
    {"person": "Jessica", "location": "Russian Hill", "avail_start": 9 * 60, "avail_end": 15 * 60, "duration": 120},                  # 540-900
    {"person": "Jason", "location": "Marina District", "avail_start": 15 * 60 + 15, "avail_end": 21 * 60 + 45, "duration": 120},     # 915-1305
    {"person": "John", "location": "North Beach", "avail_start": 9 * 60 + 45, "avail_end": 18 * 60, "duration": 15},                 # 585-1080
    {"person": "Karen", "location": "Chinatown", "avail_start": 16 * 60 + 45, "avail_end": 19 * 60, "duration": 75},                # 1005-1140
    {"person": "Sarah", "location": "Pacific Heights", "avail_start": 17 * 60 + 30, "avail_end": 18 * 60 + 15, "duration": 45},      # 1050-1095
    {"person": "Amanda", "location": "The Castro", "avail_start": 20 * 60, "avail_end": 21 * 60 + 15, "duration": 60},               # 1200-1275
    {"person": "Nancy", "location": "Nob Hill", "avail_start": 9 * 60 + 45, "avail_end": 13 * 60, "duration": 45},                   # 585-780
    {"person": "Rebecca", "location": "Sunset District", "avail_start": 8 * 60 + 45, "avail_end": 15 * 60, "duration": 75}           # 525-900 (but arrival no earlier than 9:00)
]

# Depth-first search to compute the maximum count schedule
def dfs(current_location, current_time, remaining, schedule):
    best_schedule = list(schedule)
    best_count = len(schedule)

    # Try to schedule each remaining meeting next if feasible
    for i, friend in enumerate(remaining):
        # Calculate travel time from current location to friend's meeting location
        # If for any reason the travel time is missing, skip this friend.
        if current_location not in travel_times or friend["location"] not in travel_times[current_location]:
            continue
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # The meeting can only start when both you arrive and the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if the meeting fits within the friend's available window.
        if meeting_end > friend["avail_end"]:
            continue

        # Create a meeting entry with computed start and end times.
        meeting = {
            "person": friend["person"],
            "location": friend["location"],
            "start": meeting_start,
            "end": meeting_end
        }

        new_schedule = schedule + [meeting]
        # Create a new remaining list without the scheduled friend.
        new_remaining = remaining[:i] + remaining[i+1:]
        candidate = dfs(friend["location"], meeting_end, new_remaining, new_schedule)
        if len(candidate) > best_count:
            best_schedule = candidate
            best_count = len(candidate)
    return best_schedule

def main():
    # Starting at Union Square at 9:00AM (540 minutes)
    start_location = "Union Square"
    start_time = 9 * 60  # 540 minutes

    best_schedule = dfs(start_location, start_time, friends, [])

    # Format the schedule into the required JSON structure.
    itinerary = []
    for meet in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meet["location"],
            "person": meet["person"],
            "start_time": minutes_to_timestr(meet["start"]),
            "end_time": minutes_to_timestr(meet["end"])
        })

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()