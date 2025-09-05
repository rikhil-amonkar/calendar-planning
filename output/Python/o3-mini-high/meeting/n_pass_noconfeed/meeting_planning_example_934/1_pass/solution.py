#!/usr/bin/env python
import json

def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times between locations (in minutes)
travel_times = {
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Russian Hill"): 5,
    
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Russian Hill"): 8,
    
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Russian Hill"): 18,
    
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Russian Hill"): 17,
    
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Russian Hill"): 13,
    
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Russian Hill"): 4,
    
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Russian Hill"): 7,
    
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Russian Hill"): 7,
    
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Russian Hill"): 19,
    
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Russian Hill"): 8,
    
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Marina District"): 7
}

# Define meeting constraints for each friend.
# Times are expressed in minutes from midnight.
friends = [
    {"name": "Mary", "location": "Embarcadero", "avail_start": 20 * 60, "avail_end": 21 * 60 + 15, "min_meeting": 75},
    {"name": "Kenneth", "location": "The Castro", "avail_start": 11 * 60 + 15, "avail_end": 19 * 60 + 15, "min_meeting": 30},
    {"name": "Joseph", "location": "Haight-Ashbury", "avail_start": 20 * 60, "avail_end": 22 * 60, "min_meeting": 120},
    {"name": "Sarah", "location": "Union Square", "avail_start": 11 * 60 + 45, "avail_end": 14 * 60 + 30, "min_meeting": 90},
    {"name": "Thomas", "location": "North Beach", "avail_start": 19 * 60 + 15, "avail_end": 19 * 60 + 45, "min_meeting": 15},
    {"name": "Daniel", "location": "Pacific Heights", "avail_start": 13 * 60 + 45, "avail_end": 20 * 60 + 30, "min_meeting": 15},
    {"name": "Richard", "location": "Chinatown", "avail_start": 8 * 60, "avail_end": 18 * 60 + 45, "min_meeting": 30},
    {"name": "Mark", "location": "Golden Gate Park", "avail_start": 17 * 60 + 30, "avail_end": 21 * 60 + 30, "min_meeting": 120},
    {"name": "David", "location": "Marina District", "avail_start": 20 * 60, "avail_end": 21 * 60, "min_meeting": 60},
    {"name": "Karen", "location": "Russian Hill", "avail_start": 13 * 60 + 15, "avail_end": 18 * 60 + 30, "min_meeting": 120}
]

# Global variables to store the best schedule found.
best_schedule = []
best_count = 0

def search(current_location, current_time, remaining, current_schedule):
    global best_schedule, best_count
    # Update best schedule if current one has more meetings.
    if len(current_schedule) > best_count:
        best_count = len(current_schedule)
        best_schedule = current_schedule[:]
    
    # Try scheduling each remaining friend.
    for i, friend in enumerate(remaining):
        # Ensure that a travel time exists.
        if (current_location, friend["location"]) not in travel_times:
            continue
        travel_time = travel_times[(current_location, friend["location"])]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_meeting"]
        
        # Check if the meeting can be held within friend's available window
        if meeting_end <= friend["avail_end"]:
            # Create the meeting event (times stored as numeric minutes)
            meeting_event = {
                "person": friend["name"],
                "location": friend["location"],
                "start": meeting_start,
                "end": meeting_end
            }
            new_schedule = current_schedule + [meeting_event]
            new_remaining = remaining[:i] + remaining[i+1:]
            search(friend["location"], meeting_end, new_remaining, new_schedule)

if __name__ == "__main__":
    # Start at Nob Hill at 9:00 AM (9*60 minutes)
    start_location = "Nob Hill"
    start_time = 9 * 60
    search(start_location, start_time, friends, [])
    
    # Prepare the itinerary output with properly formatted times.
    itinerary = []
    for event in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": event["location"],
            "person": event["person"],
            "start_time": format_time(event["start"]),
            "end_time": format_time(event["end"])
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))