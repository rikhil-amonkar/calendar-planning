#!/usr/bin/env python3
import json

# Define the travel times as a nested dictionary.
travel_times = {
    "Union Square": {
        "Presidio": 24,
        "Alamo Square": 15,
        "Marina District": 18,
        "Financial District": 9,
        "Nob Hill": 9,
        "Sunset District": 27,
        "Chinatown": 7,
        "Russian Hill": 13,
        "North Beach": 10,
        "Haight-Ashbury": 18
    },
    "Presidio": {
        "Union Square": 22,
        "Alamo Square": 19,
        "Marina District": 11,
        "Financial District": 23,
        "Nob Hill": 18,
        "Sunset District": 15,
        "Chinatown": 21,
        "Russian Hill": 14,
        "North Beach": 18,
        "Haight-Ashbury": 15
    },
    "Alamo Square": {
        "Union Square": 14,
        "Presidio": 17,
        "Marina District": 15,
        "Financial District": 17,
        "Nob Hill": 11,
        "Sunset District": 16,
        "Chinatown": 15,
        "Russian Hill": 13,
        "North Beach": 15,
        "Haight-Ashbury": 5
    },
    "Marina District": {
        "Union Square": 16,
        "Presidio": 10,
        "Alamo Square": 15,
        "Financial District": 17,
        "Nob Hill": 12,
        "Sunset District": 19,
        "Chinatown": 15,
        "Russian Hill": 8,
        "North Beach": 11,
        "Haight-Ashbury": 16
    },
    "Financial District": {
        "Union Square": 9,
        "Presidio": 22,
        "Alamo Square": 17,
        "Marina District": 15,
        "Nob Hill": 8,
        "Sunset District": 30,
        "Chinatown": 5,
        "Russian Hill": 11,
        "North Beach": 7,
        "Haight-Ashbury": 19
    },
    "Nob Hill": {
        "Union Square": 7,
        "Presidio": 17,
        "Alamo Square": 11,
        "Marina District": 11,
        "Financial District": 9,
        "Sunset District": 24,
        "Chinatown": 6,
        "Russian Hill": 5,
        "North Beach": 8,
        "Haight-Ashbury": 13
    },
    "Sunset District": {
        "Union Square": 30,
        "Presidio": 16,
        "Alamo Square": 17,
        "Marina District": 21,
        "Financial District": 30,
        "Nob Hill": 27,
        "Chinatown": 30,
        "Russian Hill": 24,
        "North Beach": 28,
        "Haight-Ashbury": 15
    },
    "Chinatown": {
        "Union Square": 7,
        "Presidio": 19,
        "Alamo Square": 17,
        "Marina District": 12,
        "Financial District": 5,
        "Nob Hill": 9,
        "Sunset District": 29,
        "Russian Hill": 7,
        "North Beach": 3,
        "Haight-Ashbury": 19
    },
    "Russian Hill": {
        "Union Square": 10,
        "Presidio": 14,
        "Alamo Square": 15,
        "Marina District": 7,
        "Financial District": 11,
        "Nob Hill": 5,
        "Sunset District": 23,
        "Chinatown": 9,
        "North Beach": 5,
        "Haight-Ashbury": 17
    },
    "North Beach": {
        "Union Square": 7,
        "Presidio": 17,
        "Alamo Square": 16,
        "Marina District": 9,
        "Financial District": 8,
        "Nob Hill": 7,
        "Sunset District": 27,
        "Chinatown": 6,
        "Russian Hill": 4,
        "Haight-Ashbury": 18
    },
    "Haight-Ashbury": {
        "Union Square": 19,
        "Presidio": 15,
        "Alamo Square": 5,
        "Marina District": 17,
        "Financial District": 21,
        "Nob Hill": 15,
        "Sunset District": 15,
        "Chinatown": 19,
        "Russian Hill": 17,
        "North Beach": 19
    }
}

# Define friends with their constraints.
# Times are represented as minutes after 9:00.
friends = [
    {"name": "Joshua", "location": "Marina District", "avail_start": 90, "avail_end": 315, "duration": 45},
    {"name": "Kenneth", "location": "Nob Hill", "avail_start": 225, "avail_end": 765, "duration": 30},
    {"name": "Betty", "location": "Sunset District", "avail_start": 300, "avail_end": 600, "duration": 60},
    {"name": "Kimberly", "location": "Presidio", "avail_start": 390, "avail_end": 420, "duration": 15},
    {"name": "Deborah", "location": "Chinatown", "avail_start": 495, "avail_end": 690, "duration": 15},
    {"name": "Barbara", "location": "Russian Hill", "avail_start": 510, "avail_end": 735, "duration": 120},
    {"name": "Steven", "location": "North Beach", "avail_start": 525, "avail_end": 705, "duration": 90},
    {"name": "Daniel", "location": "Haight-Ashbury", "avail_start": 570, "avail_end": 585, "duration": 15},
    {"name": "Elizabeth", "location": "Alamo Square", "avail_start": 615, "avail_end": 675, "duration": 15},
    {"name": "Sandra", "location": "Financial District", "avail_start": 630, "avail_end": 675, "duration": 45}
]

# Global variables to store best solution found.
best_schedule = []
best_count = 0

def search(current_loc, current_time, remaining, current_schedule):
    global best_schedule, best_count
    # Update best schedule if current count is higher.
    if len(current_schedule) > best_count:
        best_count = len(current_schedule)
        best_schedule = current_schedule.copy()
    
    # Try to schedule each remaining friend.
    for i, friend in enumerate(remaining):
        # Get travel time from current location to friend's location.
        if current_loc not in travel_times or friend["location"] not in travel_times[current_loc]:
            continue  # if travel time not available, skip
        t_travel = travel_times[current_loc][friend["location"]]
        arrival_time = current_time + t_travel
        # The meeting can only start once you arrive and when the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting can finish before friend's availability ends.
        if meeting_end <= friend["avail_end"]:
            new_schedule = current_schedule + [{
                "person": friend["name"],
                "location": friend["location"],
                "start": meeting_start,  # in minutes from 9:00
                "end": meeting_end
            }]
            new_remaining = remaining[:i] + remaining[i+1:]
            search(friend["location"], meeting_end, new_remaining, new_schedule)

def convert_time(minutes_after_9):
    # Convert minutes after 9:00 to 24-hour HH:MM format.
    total_minutes = 9 * 60 + minutes_after_9
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

if __name__ == '__main__':
    # Start at Union Square at 9:00 (time = 0 minutes from 9:00)
    search("Union Square", 0, friends, [])
    
    # Prepare the itinerary using the best schedule found.
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": convert_time(meeting["start"]),
            "end_time": convert_time(meeting["end"])
        })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output))