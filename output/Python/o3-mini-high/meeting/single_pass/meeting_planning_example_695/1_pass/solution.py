#!/usr/bin/env python3
import json

# Convert time in minutes to formatted string "H:MM" (24-hour format)
def minutes_to_time(t):
    hour = t // 60
    minute = t % 60
    return f"{hour}:{minute:02d}"

# Travel time dictionary for all locations.
travel_times = {
    "Bayview": {
        "Nob Hill": 20,
        "Union Square": 17,
        "Chinatown": 18,
        "The Castro": 20,
        "Presidio": 31,
        "Pacific Heights": 23,
        "Russian Hill": 23,
    },
    "Nob Hill": {
        "Bayview": 19,
        "Union Square": 7,
        "Chinatown": 6,
        "The Castro": 17,
        "Presidio": 17,
        "Pacific Heights": 8,
        "Russian Hill": 5,
    },
    "Union Square": {
        "Bayview": 15,
        "Nob Hill": 9,
        "Chinatown": 7,
        "The Castro": 19,
        "Presidio": 24,
        "Pacific Heights": 15,
        "Russian Hill": 13,
    },
    "Chinatown": {
        "Bayview": 22,
        "Nob Hill": 8,
        "Union Square": 7,
        "The Castro": 22,
        "Presidio": 19,
        "Pacific Heights": 10,
        "Russian Hill": 7,
    },
    "The Castro": {
        "Bayview": 19,
        "Nob Hill": 16,
        "Union Square": 19,
        "Chinatown": 20,
        "Presidio": 20,
        "Pacific Heights": 16,
        "Russian Hill": 18,
    },
    "Presidio": {
        "Bayview": 31,
        "Nob Hill": 18,
        "Union Square": 22,
        "Chinatown": 21,
        "The Castro": 21,
        "Pacific Heights": 11,
        "Russian Hill": 14,
    },
    "Pacific Heights": {
        "Bayview": 22,
        "Nob Hill": 8,
        "Union Square": 12,
        "Chinatown": 11,
        "The Castro": 16,
        "Presidio": 11,
        "Russian Hill": 7,
    },
    "Russian Hill": {
        "Bayview": 23,
        "Nob Hill": 5,
        "Union Square": 11,
        "Chinatown": 9,
        "The Castro": 21,
        "Presidio": 14,
        "Pacific Heights": 7,
    }
}

# Define the friend meeting constraints.
# Times are given in minutes after midnight.
# For example, 9:00 AM = 9*60 = 540
friends = [
    {
        "name": "Paul",
        "location": "Nob Hill",
        "avail_start": 16 * 60 + 15,  # 16:15
        "avail_end": 21 * 60 + 15,    # 21:15
        "duration": 60
    },
    {
        "name": "Carol",
        "location": "Union Square",
        "avail_start": 18 * 60,       # 18:00
        "avail_end": 20 * 60 + 15,    # 20:15
        "duration": 120
    },
    {
        "name": "Patricia",
        "location": "Chinatown",
        "avail_start": 20 * 60,       # 20:00
        "avail_end": 21 * 60 + 30,    # 21:30
        "duration": 75
    },
    {
        "name": "Karen",
        "location": "The Castro",
        "avail_start": 17 * 60,       # 17:00
        "avail_end": 19 * 60,         # 19:00
        "duration": 45
    },
    {
        "name": "Nancy",
        "location": "Presidio",
        "avail_start": 11 * 60 + 45,  # 11:45
        "avail_end": 22 * 60,         # 22:00
        "duration": 30
    },
    {
        "name": "Jeffrey",
        "location": "Pacific Heights",
        "avail_start": 20 * 60,       # 20:00
        "avail_end": 20 * 60 + 45,    # 20:45
        "duration": 45
    },
    {
        "name": "Matthew",
        "location": "Russian Hill",
        "avail_start": 15 * 60 + 45,  # 15:45
        "avail_end": 21 * 60 + 45,    # 21:45
        "duration": 75
    }
]

# Global variable to track the best schedule (maximizes number of meetings)
best_schedule = []

# Depth-first search to explore all possible meeting orders.
def dfs(current_time, current_location, remaining, schedule):
    global best_schedule
    # Update best_schedule if current schedule has more meetings.
    if len(schedule) > len(best_schedule):
        best_schedule = schedule.copy()
    # Try scheduling each remaining friend next.
    for i, friend in enumerate(remaining):
        # Check travel time from current location to friend's location.
        # It is assumed that the travel_times dictionary has an entry for (current_location -> friend.location)
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # The meeting can only start when the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if we can finish the meeting before the friend leaves.
        if meeting_end <= friend["avail_end"]:
            # Create a meeting record.
            meeting = {
                "person": friend["name"],
                "location": friend["location"],
                "start": meeting_start,
                "end": meeting_end
            }
            # Prepare new remaining list without the current friend.
            new_remaining = remaining[:i] + remaining[i+1:]
            dfs(meeting_end, friend["location"], new_remaining, schedule + [meeting])
    # Also, if no further friend can be scheduled, this branch terminates.

def main():
    # Start at Bayview at 9:00 AM (9*60 = 540 minutes).
    start_time = 9 * 60
    start_location = "Bayview"
    
    # Run DFS to compute the optimal schedule.
    dfs(start_time, start_location, friends, [])
    
    # Convert the best_schedule meetings to the desired itinerary format with formatted times.
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting["start"]),
            "end_time": minutes_to_time(meeting["end"])
        })
    
    # Create output dictionary.
    output = {
        "itinerary": itinerary
    }
    
    # Output the JSON-formatted result.
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()