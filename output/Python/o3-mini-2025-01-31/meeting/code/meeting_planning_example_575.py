#!/usr/bin/env python3
import json
import copy

# Helper functions for time conversion
def time_to_minutes(t_str):
    # t_str is in format "H:MM" (24-hour, no leading zero required)
    parts = t_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

# Travel times in minutes between locations.
# Keys are tuples: (origin, destination)
travel_times = {
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Russian Hill"): 18,
    
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Russian Hill"): 14,
    
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Russian Hill"): 24,
    
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Russian Hill"): 17,
    
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Russian Hill"): 15,
    
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Russian Hill"): 19,
    
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Golden Gate Park"): 21,
}

# Meeting constraints for each friend.
# Each friend meeting is represented as a dictionary with:
# person, location, start (availability start in minutes), end (availability end in minutes), and duration (minimum meeting duration in minutes)
meetings = [
    {"person": "Rebecca", "location": "Presidio", "avail_start": time_to_minutes("18:15"), "avail_end": time_to_minutes("20:45"), "duration": 60},
    {"person": "Linda", "location": "Sunset District", "avail_start": time_to_minutes("15:30"), "avail_end": time_to_minutes("19:45"), "duration": 30},
    {"person": "Elizabeth", "location": "Haight-Ashbury", "avail_start": time_to_minutes("17:15"), "avail_end": time_to_minutes("19:30"), "duration": 105},
    {"person": "William", "location": "Mission District", "avail_start": time_to_minutes("13:15"), "avail_end": time_to_minutes("19:30"), "duration": 30},
    {"person": "Robert", "location": "Golden Gate Park", "avail_start": time_to_minutes("14:15"), "avail_end": time_to_minutes("21:30"), "duration": 45},
    {"person": "Mark", "location": "Russian Hill", "avail_start": time_to_minutes("10:00"), "avail_end": time_to_minutes("21:15"), "duration": 75}
]

# Starting point and time (arrival at The Castro at 9:00)
start_location = "The Castro"
start_time = time_to_minutes("9:00")

# Global variable to store the best itinerary (max number of meetings scheduled)
best_itinerary = []

def get_travel_time(origin, destination):
    # Returns travel time between origin and destination from travel_times dictionary
    if (origin, destination) in travel_times:
        return travel_times[(origin, destination)]
    else:
        # If not explicitly provided, assume a large travel time (should not happen)
        return 999

def backtrack(current_time, current_loc, remaining, current_schedule):
    global best_itinerary
    # Update best itinerary if current schedule has more meetings than best found so far
    if len(current_schedule) > len(best_itinerary):
        best_itinerary = copy.deepcopy(current_schedule)
    # Try to schedule each remaining meeting
    for i, meeting in enumerate(remaining):
        travel = get_travel_time(current_loc, meeting["location"])
        arrival_time = current_time + travel
        # The meeting cannot start before the meeting's available start time.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if the meeting can be completed within the friend's available window.
        if meeting_end <= meeting["avail_end"]:
            # Proceed with this meeting scheduled.
            event = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": meeting_start,
                "end_time": meeting_end
            }
            new_schedule = current_schedule + [event]
            # Create new remaining list without this meeting.
            new_remaining = remaining[:i] + remaining[i+1:]
            backtrack(meeting_end, meeting["location"], new_remaining, new_schedule)
    # End recursion

def main():
    global best_itinerary
    # Run backtracking search from the starting point.
    backtrack(start_time, start_location, meetings, [])
    
    # Convert the best_itinerary times from minutes to H:MM format.
    itinerary_output = []
    for event in best_itinerary:
        itinerary_output.append({
            "action": event["action"],
            "location": event["location"],
            "person": event["person"],
            "start_time": minutes_to_time(event["start_time"]),
            "end_time": minutes_to_time(event["end_time"])
        })
    
    result = {"itinerary": itinerary_output}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()