import json
import sys
sys.setrecursionlimit(10000)

# Travel times (in minutes) between locations.
travel_times = {
    "Russian Hill": {
        "Sunset District": 23,
        "Union Square": 10,
        "Nob Hill": 5,
        "Marina District": 7,
        "Richmond District": 14,
        "Financial District": 11,
        "Embarcadero": 8,
        "The Castro": 21,
        "Alamo Square": 15,
        "Presidio": 14
    },
    "Sunset District": {
        "Russian Hill": 24,
        "Union Square": 30,
        "Nob Hill": 27,
        "Marina District": 21,
        "Richmond District": 12,
        "Financial District": 30,
        "Embarcadero": 30,
        "The Castro": 17,
        "Alamo Square": 17,
        "Presidio": 16
    },
    "Union Square": {
        "Russian Hill": 13,
        "Sunset District": 27,
        "Nob Hill": 9,
        "Marina District": 18,
        "Richmond District": 20,
        "Financial District": 9,
        "Embarcadero": 11,
        "The Castro": 17,
        "Alamo Square": 15,
        "Presidio": 24
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Sunset District": 24,
        "Union Square": 7,
        "Marina District": 11,
        "Richmond District": 14,
        "Financial District": 9,
        "Embarcadero": 9,
        "The Castro": 17,
        "Alamo Square": 11,
        "Presidio": 17
    },
    "Marina District": {
        "Russian Hill": 8,
        "Sunset District": 19,
        "Union Square": 16,
        "Nob Hill": 12,
        "Richmond District": 11,
        "Financial District": 17,
        "Embarcadero": 14,
        "The Castro": 22,
        "Alamo Square": 15,
        "Presidio": 10
    },
    "Richmond District": {
        "Russian Hill": 13,
        "Sunset District": 11,
        "Union Square": 21,
        "Nob Hill": 17,
        "Marina District": 9,
        "Financial District": 22,
        "Embarcadero": 19,
        "The Castro": 16,
        "Alamo Square": 13,
        "Presidio": 7
    },
    "Financial District": {
        "Russian Hill": 11,
        "Sunset District": 30,
        "Union Square": 9,
        "Nob Hill": 8,
        "Marina District": 15,
        "Richmond District": 21,
        "Embarcadero": 4,
        "The Castro": 20,
        "Alamo Square": 17,
        "Presidio": 22
    },
    "Embarcadero": {
        "Russian Hill": 8,
        "Sunset District": 30,
        "Union Square": 10,
        "Nob Hill": 10,
        "Marina District": 12,
        "Richmond District": 21,
        "Financial District": 5,
        "The Castro": 25,
        "Alamo Square": 19,
        "Presidio": 20
    },
    "The Castro": {
        "Russian Hill": 18,
        "Sunset District": 17,
        "Union Square": 19,
        "Nob Hill": 16,
        "Marina District": 21,
        "Richmond District": 16,
        "Financial District": 21,
        "Embarcadero": 22,
        "Alamo Square": 8,
        "Presidio": 20
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Sunset District": 16,
        "Union Square": 14,
        "Nob Hill": 11,
        "Marina District": 15,
        "Richmond District": 11,
        "Financial District": 17,
        "Embarcadero": 16,
        "The Castro": 8,
        "Presidio": 17
    },
    "Presidio": {
        "Russian Hill": 14,
        "Sunset District": 15,
        "Union Square": 22,
        "Nob Hill": 18,
        "Marina District": 11,
        "Richmond District": 7,
        "Financial District": 23,
        "Embarcadero": 20,
        "The Castro": 21,
        "Alamo Square": 19
    }
}

# Define each friend's meeting constraints.
# Times are represented in minutes after midnight.
# For example, 9:00AM is 9 * 60 = 540.
friends = [
    {"person": "David", "location": "Sunset District", "avail_start": 555, "avail_end": 1320, "duration": 15},
    {"person": "Kenneth", "location": "Union Square", "avail_start": 1275, "avail_end": 1305, "duration": 15},
    {"person": "Patricia", "location": "Nob Hill", "avail_start": 900, "avail_end": 1155, "duration": 120},
    {"person": "Mary", "location": "Marina District", "avail_start": 885, "avail_end": 1005, "duration": 45},
    {"person": "Charles", "location": "Richmond District", "avail_start": 1035, "avail_end": 1260, "duration": 15},
    {"person": "Joshua", "location": "Financial District", "avail_start": 870, "avail_end": 1035, "duration": 90},
    {"person": "Ronald", "location": "Embarcadero", "avail_start": 1095, "avail_end": 1245, "duration": 30},
    {"person": "George", "location": "The Castro", "avail_start": 855, "avail_end": 1140, "duration": 105},
    {"person": "Kimberly", "location": "Alamo Square", "avail_start": 540, "avail_end": 870, "duration": 105},
    {"person": "William", "location": "Presidio", "avail_start": 420, "avail_end": 765, "duration": 60}
]

# Global variables for the best (maximum count) itinerary found.
best_schedule = []
best_count = 0

def format_time(minutes):
    """Convert minutes after midnight to H:MM (24-hour) format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def search_itinerary(current_loc, current_time, remaining, current_itinerary):
    global best_schedule, best_count
    # Update best_schedule if the current itinerary has more meetings.
    if len(current_itinerary) > best_count:
        best_count = len(current_itinerary)
        best_schedule = current_itinerary.copy()
    
    # Try scheduling a meeting with each friend not yet visited.
    for i, friend in enumerate(remaining):
        # Compute travel time from current location to friend's location.
        if current_loc not in travel_times or friend["location"] not in travel_times[current_loc]:
            continue  # Skip if no travel time available.
        travel = travel_times[current_loc][friend["location"]]
        arrival_time = current_time + travel
        # Meeting can only start after the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        if meeting_end <= friend["avail_end"]:
            meeting = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["person"],
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            }
            # Prepare a new list of remaining friends without the current one.
            new_remaining = remaining[:i] + remaining[i+1:]
            search_itinerary(friend["location"], meeting_end, new_remaining, current_itinerary + [meeting])

def main():
    # Starting parameters: Begin at Russian Hill at 9:00AM (540 minutes).
    start_location = "Russian Hill"
    start_time = 540  # 9:00 AM
    search_itinerary(start_location, start_time, friends, [])
    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()