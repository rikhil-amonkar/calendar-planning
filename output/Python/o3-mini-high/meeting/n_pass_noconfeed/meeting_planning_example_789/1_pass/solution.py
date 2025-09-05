#!/usr/bin/env python3
import json
import copy

# Helper function to convert minutes-since-midnight to "H:MM" 24-hour string.
def format_time(t):
    hour = t // 60
    minute = t % 60
    return f"{hour}:{minute:02d}"

# Travel times (in minutes) between locations, stored as a dictionary with keys (from, to)
travel_times = {
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Sunset District"): 27,

    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Sunset District"): 23,

    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Sunset District"): 16,

    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,

    ("Marina District", "Union Square"): 16,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Sunset District"): 19,

    ("Bayview", "Union Square"): 18,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Sunset District"): 23,

    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Sunset District"): 29,

    ("Presidio", "Union Square"): 22,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,

    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Presidio"): 16,
}

# Meeting information for each friend.
# Time values are in minutes from midnight.
# For example, 9:00AM = 9*60; 16:45 = 16*60+45.
meetings = [
    {
        "person": "Betty",
        "location": "Russian Hill",
        "available_start": 7 * 60,         # 7:00
        "available_end": 16 * 60 + 45,       # 16:45
        "min_duration": 105
    },
    {
        "person": "Melissa",
        "location": "Alamo Square",
        "available_start": 9 * 60 + 30,      # 9:30
        "available_end": 17 * 60 + 15,       # 17:15
        "min_duration": 105
    },
    {
        "person": "Joshua",
        "location": "Haight-Ashbury",
        "available_start": 12 * 60 + 15,     # 12:15
        "available_end": 19 * 60,            # 19:00
        "min_duration": 90
    },
    {
        "person": "Jeffrey",
        "location": "Marina District",
        "available_start": 12 * 60 + 15,     # 12:15
        "available_end": 18 * 60,            # 18:00
        "min_duration": 45
    },
    {
        "person": "James",
        "location": "Bayview",
        "available_start": 7 * 60 + 30,      # 7:30
        "available_end": 20 * 60,            # 20:00
        "min_duration": 90
    },
    {
        "person": "Anthony",
        "location": "Chinatown",
        "available_start": 11 * 60 + 45,     # 11:45
        "available_end": 13 * 60 + 30,       # 13:30
        "min_duration": 75
    },
    {
        "person": "Timothy",
        "location": "Presidio",
        "available_start": 12 * 60 + 30,     # 12:30
        "available_end": 14 * 60 + 45,       # 14:45
        "min_duration": 90
    },
    {
        "person": "Emily",
        "location": "Sunset District",
        "available_start": 19 * 60 + 30,     # 19:30
        "available_end": 21 * 60 + 30,       # 21:30
        "min_duration": 120
    }
]

# Global best schedule (list of scheduled meeting entries) and best count
best_schedule = []
best_count = 0

# Recursive DFS to try all meeting orders that satisfy travel and meeting constraints.
def search(current_time, current_location, scheduled, remaining):
    global best_schedule, best_count

    # If no more meetings can be scheduled, update best schedule if count is higher.
    if len(scheduled) > best_count:
        best_schedule = copy.deepcopy(scheduled)
        best_count = len(scheduled)
    
    # Try each meeting in the remaining list.
    for i, meeting in enumerate(remaining):
        # Check travel time from current_location to meeting's location.
        if (current_location, meeting["location"]) not in travel_times:
            continue
        travel = travel_times[(current_location, meeting["location"])]
        arrival_time = current_time + travel
        # The meeting can only start when the friend is available.
        proposed_start = max(arrival_time, meeting["available_start"])
        finish_time = proposed_start + meeting["min_duration"]
        # If the meeting would finish after the friend leaves, skip this meeting.
        if finish_time > meeting["available_end"]:
            continue
        
        # Create a scheduled record for this meeting.
        scheduled_entry = {
            "person": meeting["person"],
            "location": meeting["location"],
            "start": proposed_start,
            "end": finish_time
        }
        
        new_scheduled = scheduled + [scheduled_entry]
        new_remaining = remaining[:i] + remaining[i+1:]
        
        # Continue searching from the end time and new location.
        search(finish_time, meeting["location"], new_scheduled, new_remaining)

# Main routine
def main():
    # You arrive at Union Square at 9:00AM = 540 minutes
    start_time = 9 * 60
    start_location = "Union Square"
    
    # Run the recursive search
    search(start_time, start_location, [], meetings)
    
    # Build the itinerary from the best_schedule found.
    # Each entry's time is converted to a string "H:MM" (24-hour format, no leading zero for hour).
    itinerary = []
    for entry in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": entry["location"],
            "person": entry["person"],
            "start_time": format_time(entry["start"]),
            "end_time": format_time(entry["end"])
        })
    
    result = {"itinerary": itinerary}
    # Output JSON-formatted result.
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()