import json

# Define helper functions to convert between time formats (minutes from midnight to H:MM string)
def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define the travel times dictionary in both directions.
# We'll store as travel_times[from_location][to_location] = minutes
travel_times = {
    "Richmond District": {
        "The Castro": 16, "Nob Hill": 17, "Marina District": 9, "Pacific Heights": 10,
        "Haight-Ashbury": 10, "Mission District": 20, "Chinatown": 20, "Russian Hill": 13,
        "Alamo Square": 13, "Bayview": 27
    },
    "The Castro": {
        "Richmond District": 16, "Nob Hill": 16, "Marina District": 21, "Pacific Heights": 16,
        "Haight-Ashbury": 6, "Mission District": 7, "Chinatown": 22, "Russian Hill": 18,
        "Alamo Square": 8, "Bayview": 19
    },
    "Nob Hill": {
        "Richmond District": 14, "The Castro": 17, "Marina District": 11, "Pacific Heights": 8,
        "Haight-Ashbury": 13, "Mission District": 13, "Chinatown": 6, "Russian Hill": 5,
        "Alamo Square": 11, "Bayview": 19
    },
    "Marina District": {
        "Richmond District": 11, "The Castro": 22, "Nob Hill": 12, "Pacific Heights": 7,
        "Haight-Ashbury": 16, "Mission District": 20, "Chinatown": 15, "Russian Hill": 8,
        "Alamo Square": 15, "Bayview": 27
    },
    "Pacific Heights": {
        "Richmond District": 12, "The Castro": 16, "Nob Hill": 8, "Marina District": 6,
        "Haight-Ashbury": 11, "Mission District": 15, "Chinatown": 11, "Russian Hill": 7,
        "Alamo Square": 10, "Bayview": 22
    },
    "Haight-Ashbury": {
        "Richmond District": 10, "The Castro": 6, "Nob Hill": 15, "Marina District": 17,
        "Pacific Heights": 12, "Mission District": 11, "Chinatown": 19, "Russian Hill": 17,
        "Alamo Square": 5, "Bayview": 18
    },
    "Mission District": {
        "Richmond District": 20, "The Castro": 7, "Nob Hill": 12, "Marina District": 19,
        "Pacific Heights": 16, "Haight-Ashbury": 12, "Chinatown": 16, "Russian Hill": 15,
        "Alamo Square": 11, "Bayview": 14
    },
    "Chinatown": {
        "Richmond District": 20, "The Castro": 22, "Nob Hill": 9, "Marina District": 12,
        "Pacific Heights": 10, "Haight-Ashbury": 19, "Mission District": 17, "Russian Hill": 7,
        "Alamo Square": 17, "Bayview": 20
    },
    "Russian Hill": {
        "Richmond District": 14, "The Castro": 21, "Nob Hill": 5, "Marina District": 7,
        "Pacific Heights": 7, "Haight-Ashbury": 17, "Mission District": 16,
        "Chinatown": 9, "Alamo Square": 15, "Bayview": 23
    },
    "Alamo Square": {
        "Richmond District": 11, "The Castro": 8, "Nob Hill": 11, "Marina District": 15,
        "Pacific Heights": 10, "Haight-Ashbury": 5, "Mission District": 10,
        "Chinatown": 15, "Russian Hill": 13, "Bayview": 16
    },
    "Bayview": {
        "Richmond District": 25, "The Castro": 19, "Nob Hill": 20, "Marina District": 27,
        "Pacific Heights": 23, "Haight-Ashbury": 19, "Mission District": 13,
        "Chinatown": 19, "Russian Hill": 23, "Alamo Square": 16
    }
}

# Meeting constraints for each friend.
# Times will be represented as minutes from midnight.
meetings = [
    {
        "person": "Matthew",
        "location": "The Castro",
        "avail_start": 16*60 + 30,  # 16:30
        "avail_end": 20*60,         # 20:00
        "min_duration": 45
    },
    {
        "person": "Rebecca",
        "location": "Nob Hill",
        "avail_start": 15*60 + 15,  # 15:15
        "avail_end": 19*60 + 15,    # 19:15
        "min_duration": 105
    },
    {
        "person": "Brian",
        "location": "Marina District",
        "avail_start": 14*60 + 15,  # 14:15
        "avail_end": 22*60,         # 22:00
        "min_duration": 30
    },
    {
        "person": "Emily",
        "location": "Pacific Heights",
        "avail_start": 11*60 + 15,  # 11:15
        "avail_end": 19*60 + 45,    # 19:45
        "min_duration": 15
    },
    {
        "person": "Karen",
        "location": "Haight-Ashbury",
        "avail_start": 11*60 + 45,  # 11:45
        "avail_end": 17*60 + 30,    # 17:30
        "min_duration": 30
    },
    {
        "person": "Stephanie",
        "location": "Mission District",
        "avail_start": 13*60,       # 13:00
        "avail_end": 15*60 + 45,      # 15:45
        "min_duration": 75
    },
    {
        "person": "James",
        "location": "Chinatown",
        "avail_start": 14*60 + 30,   # 14:30
        "avail_end": 19*60,          # 19:00
        "min_duration": 120
    },
    {
        "person": "Steven",
        "location": "Russian Hill",
        "avail_start": 14*60,        # 14:00
        "avail_end": 20*60,          # 20:00
        "min_duration": 30
    },
    {
        "person": "Elizabeth",
        "location": "Alamo Square",
        "avail_start": 13*60,        # 13:00
        "avail_end": 17*60 + 15,       # 17:15
        "min_duration": 120
    },
    {
        "person": "William",
        "location": "Bayview",
        "avail_start": 18*60 + 15,     # 18:15
        "avail_end": 20*60 + 15,       # 20:15
        "min_duration": 90
    },
]

# Starting point and time:
start_location = "Richmond District"
start_time = 9 * 60  # 9:00 in minutes

# We'll perform a recursive search (backtracking) to try all orders that can be scheduled feasibly.
# Our goal is to maximize the number of meetings.
best_schedule = []
best_count = 0

def backtrack(current_location, current_time, remaining_meetings, current_schedule):
    global best_schedule, best_count

    # Update best schedule if current_schedule is better (more meetings scheduled)
    if len(current_schedule) > best_count:
        best_count = len(current_schedule)
        best_schedule = current_schedule.copy()
    
    for i, meeting in enumerate(remaining_meetings):
        dest = meeting["location"]
        # Get travel time from current_location to dest.
        if current_location in travel_times and dest in travel_times[current_location]:
            travel_time = travel_times[current_location][dest]
        else:
            # If no route is defined, skip
            continue
        
        arrival_time = current_time + travel_time
        # The meeting can only start when both you arrive and the friend is available.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["min_duration"]
        
        # Check if meeting_end fits within friend's available window.
        if meeting_end > meeting["avail_end"]:
            continue  # Cannot meet this friend given current schedule
        
        # Create a scheduled meeting entry.
        meeting_entry = {
            "action": "meet",
            "location": dest,
            "person": meeting["person"],
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        }
        
        # Prepare the new remaining list without the scheduled meeting.
        new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
        # Recurse: Now the current location is dest, and time is meeting_end.
        backtrack(dest, meeting_end, new_remaining, current_schedule + [meeting_entry])

# Start the backtracking with the starting location and time.
backtrack(start_location, start_time, meetings, [])

# Prepare the JSON output dictionary. Use the best_schedule found.
output = {"itinerary": best_schedule}

print(json.dumps(output, indent=2))
                    
if __name__ == "__main__":
    pass