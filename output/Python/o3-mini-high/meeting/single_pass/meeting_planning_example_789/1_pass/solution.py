#!/usr/bin/env python3
import json

# Define travel times (in minutes) between locations
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
    ("Sunset District", "Presidio"): 16
}

# Meeting constraints for each friend.
# Times are converted to minutes after midnight.
friends = [
    {
        "name": "Betty",
        "location": "Russian Hill",
        "avail_start": 7 * 60,              # 7:00
        "avail_end": 16 * 60 + 45,          # 16:45
        "duration": 105
    },
    {
        "name": "Melissa",
        "location": "Alamo Square",
        "avail_start": 9 * 60 + 30,         # 9:30
        "avail_end": 17 * 60 + 15,          # 17:15
        "duration": 105
    },
    {
        "name": "Joshua",
        "location": "Haight-Ashbury",
        "avail_start": 12 * 60 + 15,        # 12:15
        "avail_end": 19 * 60,               # 19:00
        "duration": 90
    },
    {
        "name": "Jeffrey",
        "location": "Marina District",
        "avail_start": 12 * 60 + 15,        # 12:15
        "avail_end": 18 * 60,               # 18:00
        "duration": 45
    },
    {
        "name": "James",
        "location": "Bayview",
        "avail_start": 7 * 60 + 30,         # 7:30
        "avail_end": 20 * 60,               # 20:00
        "duration": 90
    },
    {
        "name": "Anthony",
        "location": "Chinatown",
        "avail_start": 11 * 60 + 45,        # 11:45
        "avail_end": 13 * 60 + 30,          # 13:30
        "duration": 75
    },
    {
        "name": "Timothy",
        "location": "Presidio",
        "avail_start": 12 * 60 + 30,        # 12:30
        "avail_end": 14 * 60 + 45,          # 14:45
        "duration": 90
    },
    {
        "name": "Emily",
        "location": "Sunset District",
        "avail_start": 19 * 60 + 30,        # 19:30
        "avail_end": 21 * 60 + 30,          # 21:30
        "duration": 120
    }
]

# Function to convert minutes into 24-hour time string "H:MM"
def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Global variables to hold the best (maximum count) schedule found.
best_schedule = []
best_count = 0

# Backtracking search to build feasible itineraries.
def backtrack(current_loc, current_time, visited, schedule):
    global best_schedule, best_count
    # Update best schedule if the current schedule has more meetings.
    if len(schedule) > best_count:
        best_count = len(schedule)
        best_schedule = schedule.copy()
    
    # Try to add each friend that hasn't been visited yet.
    for friend in friends:
        if friend["name"] in visited:
            continue
        # Get travel time from current location to friend's location.
        key = (current_loc, friend["location"])
        # Skip if no travel time defined (should not happen with provided data)
        if key not in travel_times:
            continue
        travel_time = travel_times[key]
        arrival_time = current_time + travel_time
        # Meeting can only begin when both you arrive and the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting can finish before the friend leaves.
        if meeting_end <= friend["avail_end"]:
            event = {
                "person": friend["name"],
                "location": friend["location"],
                "start": meeting_start,
                "end": meeting_end
            }
            visited.add(friend["name"])
            schedule.append(event)
            backtrack(friend["location"], meeting_end, visited, schedule)
            schedule.pop()
            visited.remove(friend["name"])

def main():
    # You arrive at Union Square at 9:00 AM (9*60 minutes)
    start_location = "Union Square"
    start_time = 9 * 60
    backtrack(start_location, start_time, set(), [])
    
    # Prepare the itinerary for JSON output.
    itinerary = []
    for event in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": event["location"],
            "person": event["person"],
            "start_time": format_time(event["start"]),
            "end_time": format_time(event["end"])
        })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()