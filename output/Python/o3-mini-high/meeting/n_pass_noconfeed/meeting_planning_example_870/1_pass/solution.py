import json
import sys
import math

# Convert time string "H:MM" to minutes since midnight
def time_to_minutes(t):
    parts = t.split(':')
    return int(parts[0]) * 60 + int(parts[1])

# Convert minutes since midnight to time string "H:MM" (no leading zero for hour)
def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel times in minutes between locations
travel_times = {
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Russian Hill"): 7,

    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Russian Hill"): 8,

    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Russian Hill"): 18,

    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Russian Hill"): 13,

    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Russian Hill"): 13,

    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Russian Hill"): 11,

    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Russian Hill"): 14,

    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Russian Hill"): 15,

    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Russian Hill"): 5,

    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Nob Hill"): 5,
}

def get_travel_time(start_loc, end_loc):
    return travel_times.get((start_loc, end_loc), math.inf)

# Meeting constraints: each meeting has a fixed location, available window (in minutes since midnight), and a required duration.
meetings = [
    {"person": "Linda",    "location": "Marina District",  "avail_start": time_to_minutes("18:00"), "avail_end": time_to_minutes("22:00"), "duration": 30},
    {"person": "Kenneth",  "location": "The Castro",       "avail_start": time_to_minutes("14:45"), "avail_end": time_to_minutes("16:15"), "duration": 30},
    {"person": "Kimberly", "location": "Richmond District","avail_start": time_to_minutes("14:15"), "avail_end": time_to_minutes("22:00"), "duration": 30},
    {"person": "Paul",     "location": "Alamo Square",     "avail_start": time_to_minutes("21:00"), "avail_end": time_to_minutes("21:30"), "duration": 15},
    {"person": "Carol",    "location": "Financial District","avail_start": time_to_minutes("10:15"), "avail_end": time_to_minutes("12:00"), "duration": 60},
    {"person": "Brian",    "location": "Presidio",         "avail_start": time_to_minutes("10:00"), "avail_end": time_to_minutes("21:30"), "duration": 75},
    {"person": "Laura",    "location": "Mission District", "avail_start": time_to_minutes("16:15"), "avail_end": time_to_minutes("20:30"), "duration": 30},
    {"person": "Sandra",   "location": "Nob Hill",         "avail_start": time_to_minutes("9:15"),  "avail_end": time_to_minutes("18:30"), "duration": 60},
    {"person": "Karen",    "location": "Russian Hill",     "avail_start": time_to_minutes("18:30"), "avail_end": time_to_minutes("22:00"), "duration": 75},
]

# Global variables to track the best schedule found
best_schedule = []
best_count = 0
best_finish = math.inf

# Recursive search function for feasible schedules.
def search(current_time, current_loc, schedule, remaining):
    global best_schedule, best_count, best_finish

    # Update best schedule if this one has more meetings, or same number but finishes earlier.
    if len(schedule) > best_count or (len(schedule) == best_count and current_time < best_finish):
        best_schedule = schedule[:]
        best_count = len(schedule)
        best_finish = current_time

    # Try scheduling each remaining meeting next if feasible.
    for i, meet in enumerate(remaining):
        # Calculate travel time to the meeting's location.
        travel = get_travel_time(current_loc, meet["location"])
        arrival_time = current_time + travel

        # The meeting cannot start before both arrival and its available window start.
        meeting_start = max(arrival_time, meet["avail_start"])
        meeting_end = meeting_start + meet["duration"]

        # Check if meeting can be completed within the available window.
        if meeting_end <= meet["avail_end"]:
            # Create a schedule entry for this meeting.
            event = {
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_schedule = schedule + [event]
            new_remaining = remaining[:i] + remaining[i+1:]
            # Recurse from the end time and location of this meeting.
            search(meeting_end, meet["location"], new_schedule, new_remaining)

# Main execution starts here.
if __name__ == "__main__":
    # Starting point: You arrive at Pacific Heights at 9:00 AM (9:00 = 540 minutes).
    start_time = time_to_minutes("9:00")
    start_location = "Pacific Heights"
    
    # Begin the recursive search for an optimal schedule.
    search(start_time, start_location, [], meetings)
    
    # Prepare the result dictionary and output it as JSON.
    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))