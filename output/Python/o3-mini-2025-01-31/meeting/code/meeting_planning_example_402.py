#!/usr/bin/env python3
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define travel times (in minutes) as a dictionary with keys (from, to)
travel_times = {
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 17,
    
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Union Square"): 30,
    
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Union Square"): 16,
    
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Union Square"): 9,
    
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Financial District"): 9,
    
    # For reverse lookups if not included explicitly:
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Financial District", "Golden Gate Park"): 23,
    ("Union Square", "Golden Gate Park"): 22
}

# Participant constraints: (person, location, availability_start, availability_end, min_meeting_duration)
# Times are expressed in minutes since midnight.
participants = [
    {"person": "Matthew", "location": "Marina District", "avail_start": 9 * 60 + 15, "avail_end": 12 * 60, "duration": 15},
    {"person": "Robert", "location": "Union Square",   "avail_start": 10 * 60 + 15, "avail_end": 21 * 60 + 45, "duration": 15},
    {"person": "Joseph", "location": "Financial District", "avail_start": 14 * 60 + 15, "avail_end": 18 * 60 + 45, "duration": 30},
    {"person": "Patricia", "location": "Sunset District", "avail_start": 17 * 60, "avail_end": 19 * 60 + 45, "duration": 45},
    {"person": "Sarah", "location": "Haight-Ashbury", "avail_start": 17 * 60, "avail_end": 21 * 60 + 30, "duration": 105}
]

# We start at Golden Gate Park at 9:00 (which is 9*60 = 540 minutes)
current_location = "Golden Gate Park"
current_time = 9 * 60  # 9:00 AM

# We will build a simple itinerary following an order that fits all constraints.
# After analyzing the time windows and travel times, we choose the following order:
# 1. Matthew at Marina District
# 2. Robert at Union Square
# 3. Joseph at Financial District
# 4. Patricia at Sunset District
# 5. Sarah at Haight-Ashbury

order = ["Matthew", "Robert", "Joseph", "Patricia", "Sarah"]

# Build a lookup for participant details
participant_lookup = {p["person"]: p for p in participants}

itinerary = []

def travel_time(from_loc, to_loc):
    # Return the travel time if the tuple key exists, otherwise try reversed key.
    if (from_loc, to_loc) in travel_times:
        return travel_times[(from_loc, to_loc)]
    elif (to_loc, from_loc) in travel_times:
        return travel_times[(to_loc, from_loc)]
    else:
        # Default travel time if not defined
        return 10

for person in order:
    details = participant_lookup[person]
    destination = details["location"]
    # Compute travel from current_location to destination:
    t_time = travel_time(current_location, destination)
    current_time += t_time  # travel time added
    # If arrived before the availability window, wait until avail_start:
    meeting_start = max(current_time, details["avail_start"])
    meeting_end = meeting_start + details["duration"]
    # Check that meeting finishes before participant's avail_end (assume it's feasible)
    if meeting_end > details["avail_end"]:
        # If not feasible, adjust meeting_end to avail_end
        meeting_end = details["avail_end"]
    # Add meeting to itinerary
    itinerary.append({
        "action": "meet",
        "location": destination,
        "person": person,
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    # Update current_time and current_location for next leg
    current_time = meeting_end
    current_location = destination

# Prepare the result dictionary
result = {"itinerary": itinerary}

# Output the result as JSON
print(json.dumps(result, indent=2))
                    
if __name__ == "__main__":
    pass