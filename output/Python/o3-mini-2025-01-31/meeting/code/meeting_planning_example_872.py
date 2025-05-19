#!/usr/bin/env python3
import json

def time_to_minutes(time_str):
    # time_str in format "H:MM" or "HH:MM" (24-hr)
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    # Hours should be printed without a leading zero.
    return f"{hours}:{mins:02d}"

# Predefined travel times (in minutes) between locations (directional)
travel_times = {
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Marina District"): 11,
    
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Marina District"): 17,
    
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Marina District"): 11,
    
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Marina District"): 7,
    
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Marina District"): 9,
    
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Marina District"): 12,
    
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Marina District"): 18,
    
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Marina District"): 12,
    
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Marina District"): 15,
    
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Financial District"): 17,
}

# Meeting constraints for each friend.
# Times are represented as minutes from midnight.
meetings = [
    {
        "person": "Jason",
        "location": "Chinatown",
        "avail_start": time_to_minutes("8:15"),
        "avail_end": time_to_minutes("11:45"),
        "min_duration": 75
    },
    {
        "person": "Mark",
        "location": "Marina District",
        "avail_start": time_to_minutes("10:15"),
        "avail_end": time_to_minutes("13:00"),
        "min_duration": 75
    },
    {
        "person": "Kenneth",
        "location": "North Beach",
        "avail_start": time_to_minutes("9:45"),
        "avail_end": time_to_minutes("21:00"),
        "min_duration": 30
    },
    {
        "person": "Kimberly",
        "location": "Embarcadero",
        "avail_start": time_to_minutes("9:45"),
        "avail_end": time_to_minutes("19:30"),
        "min_duration": 75
    },
    {
        "person": "Jessica",
        "location": "Nob Hill",
        "avail_start": time_to_minutes("13:45"),
        "avail_end": time_to_minutes("21:00"),
        "min_duration": 90
    },
    {
        "person": "Stephanie",
        "location": "Union Square",
        "avail_start": time_to_minutes("14:45"),
        "avail_end": time_to_minutes("18:45"),
        "min_duration": 105
    },
    {
        "person": "Brian",
        "location": "Russian Hill",
        "avail_start": time_to_minutes("15:30"),
        "avail_end": time_to_minutes("21:45"),
        "min_duration": 60
    },
    {
        "person": "Steven",
        "location": "Financial District",
        "avail_start": time_to_minutes("7:15"),
        "avail_end": time_to_minutes("21:15"),
        "min_duration": 60
    },
    {
        "person": "Karen",
        "location": "Haight-Ashbury",
        "avail_start": time_to_minutes("21:00"),
        "avail_end": time_to_minutes("21:45"),
        "min_duration": 45
    }
]

# Define the order in which meetings will be attempted.
# This ordering is chosen to respect the availability windows and travel constraints.
order = ["Jason", "Mark", "Kenneth", "Kimberly", "Jessica", "Stephanie", "Brian", "Steven", "Karen"]

# Starting point: Arrive at Presidio at 9:00AM.
current_time = time_to_minutes("9:00")
current_location = "Presidio"

# Build a lookup for meetings by person for easier ordering.
meeting_lookup = {m["person"]: m for m in meetings}

itinerary = []

for person in order:
    meeting = meeting_lookup[person]
    destination = meeting["location"]
    # Get travel time from current location to destination.
    # If direct tuple is not found, assume symmetric value from reverse direction.
    if (current_location, destination) in travel_times:
        travel = travel_times[(current_location, destination)]
    elif (destination, current_location) in travel_times:
        travel = travel_times[(destination, current_location)]
    else:
        # If no travel time is provided, default to a large number.
        travel = 999
    # Arrive at destination.
    arrival_time = current_time + travel
    # The meeting can only start when both we have arrived and the friend is available.
    meeting_start = max(arrival_time, meeting["avail_start"])
    meeting_end = meeting_start + meeting["min_duration"]
    
    # Check if meeting can be completed within the friend's availability.
    if meeting_end > meeting["avail_end"]:
        # If cannot meet, then skip this meeting.
        continue

    # Append the meeting event.
    itinerary.append({
        "action": "meet",
        "location": destination,
        "person": person,
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    
    # Update current time and location.
    current_time = meeting_end
    current_location = destination

# Output as the JSON formatted dictionary.
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))