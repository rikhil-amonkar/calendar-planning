#!/usr/bin/env python3
import json

# Convert time (in minutes from midnight) to string "H:MM"
def minutes_to_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define the travel times (in minutes) as provided
travel_times = {
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Russian Hill"): 8,
    
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Russian Hill"): 15,
    
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Russian Hill"): 14,
    
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Russian Hill"): 13,
    
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Russian Hill"): 24,
    
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Russian Hill"): 11,
    
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Russian Hill"): 17,
    
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Haight-Ashbury"): 17
}

# Define the meeting constraints
# Times are in minutes from midnight.
# Arrival at Marina District at 9:00 AM -> 9*60 = 540
# Meeting availabilities and durations:
# Karen: Mission District, 14:15 (855) to 22:00 (1320), duration 30.
# Richard: Fisherman's Wharf, 14:30 (870) to 17:30 (1050), duration 30.
# Robert: Presidio, 21:45 (1305) to 22:45 (1365), duration 60.
# Joseph: Union Square, 11:45 (705) to 14:45 (885), duration 120.
# Helen: Sunset District, 14:45 (885) to 20:45 (1245), duration 105.
# Elizabeth: Financial District, 10:00 (600) to 12:45 (765), duration 75.
# Kimberly: Haight-Ashbury, 14:15 (855) to 17:30 (1050), duration 105.
# Ashley: Russian Hill, 11:30 (690) to 21:30 (1290), duration 45.
meetings = [
    {"person": "Karen", "location": "Mission District", "avail_start": 855, "avail_end": 1320, "duration": 30},
    {"person": "Richard", "location": "Fisherman's Wharf", "avail_start": 870, "avail_end": 1050, "duration": 30},
    {"person": "Robert", "location": "Presidio", "avail_start": 1305, "avail_end": 1365, "duration": 60},
    {"person": "Joseph", "location": "Union Square", "avail_start": 705, "avail_end": 885, "duration": 120},
    {"person": "Helen", "location": "Sunset District", "avail_start": 885, "avail_end": 1245, "duration": 105},
    {"person": "Elizabeth", "location": "Financial District", "avail_start": 600, "avail_end": 765, "duration": 75},
    {"person": "Kimberly", "location": "Haight-Ashbury", "avail_start": 855, "avail_end": 1050, "duration": 105},
    {"person": "Ashley", "location": "Russian Hill", "avail_start": 690, "avail_end": 1290, "duration": 45}
]

# Global variable to store the best (maximum meetings) itinerary found.
best_itinerary = []

# Depth First Search to explore all feasible meeting orders.
def dfs(current_time, current_location, remaining_meetings, current_schedule):
    global best_itinerary
    # Update best if current schedule has more meetings
    if len(current_schedule) > len(best_itinerary):
        best_itinerary = current_schedule[:]  # copy current schedule

    # Try each remaining meeting in turn.
    for i, meeting in enumerate(remaining_meetings):
        # Check travel time from current location to meeting location.
        if (current_location, meeting["location"]) not in travel_times:
            continue
        travel_time = travel_times[(current_location, meeting["location"])]
        arrival_time = current_time + travel_time
        # The meeting can only start when both arrived and the availability window starts.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if the meeting can finish before the person's availability ends.
        if meeting_end <= meeting["avail_end"]:
            # Create an event dictionary for this meeting.
            event = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_str(meeting_start),
                "end_time": minutes_to_str(meeting_end)
            }
            # Prepare new schedule and remaining list.
            next_schedule = current_schedule + [event]
            next_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            # Recurse from new state.
            dfs(meeting_end, meeting["location"], next_remaining, next_schedule)

if __name__ == '__main__':
    # Starting point: Marina District at 9:00 (540 minutes)
    start_time = 540
    start_location = "Marina District"
    dfs(start_time, start_location, meetings, [])
    
    # Prepare final result in the specified JSON format.
    result = {
        "itinerary": best_itinerary
    }
    
    # Output the resulting itinerary as JSON.
    print(json.dumps(result, indent=2))