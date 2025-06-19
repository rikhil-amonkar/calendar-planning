import json

def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return hour * 60 + minutes

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

travel_times = {
    "Union Square": {
        "The Castro": 17, "North Beach": 10, "Embarcadero": 11, "Alamo Square": 15,
        "Nob Hill": 9, "Presidio": 24, "Fisherman's Wharf": 15, "Mission District": 14, "Haight-Ashbury": 18
    },
    "The Castro": {
        "Union Square": 19, "North Beach": 20, "Embarcadero": 22, "Alamo Square": 8,
        "Nob Hill": 16, "Presidio": 20, "Fisherman's Wharf": 24, "Mission District": 7, "Haight-Ashbury": 6
    },
    "North Beach": {
        "Union Square": 7, "The Castro": 23, "Embarcadero": 6, "Alamo Square": 16,
        "Nob Hill": 7, "Presidio": 17, "Fisherman's Wharf": 5, "Mission District": 18, "Haight-Ashbury": 18
    },
    "Embarcadero": {
        "Union Square": 10, "The Castro": 25, "North Beach": 5, "Alamo Square": 19,
        "Nob Hill": 10, "Presidio": 20, "Fisherman's Wharf": 6, "Mission District": 20, "Haight-Ashbury": 21
    },
    "Alamo Square": {
        "Union Square": 14, "The Castro": 8, "North Beach": 15, "Embarcadero": 16,
        "Nob Hill": 11, "Presidio": 17, "Fisherman's Wharf": 19, "Mission District": 10, "Haight-Ashbury": 5
    },
    "Nob Hill": {
        "Union Square": 7, "The Castro": 17, "North Beach": 8, "Embarcadero": 9,
        "Alamo Square": 11, "Presidio": 17, "Fisherman's Wharf": 10, "Mission District": 13, "Haight-Ashbury": 13
    },
    "Presidio": {
        "Union Square": 22, "The Castro": 21, "North Beach": 18, "Embarcadero": 20,
        "Alamo Square": 19, "Nob Hill": 18, "Fisherman's Wharf": 19, "Mission District": 26, "Haight-Ashbury": 15
    },
    "Fisherman's Wharf": {
        "Union Square": 13, "The Castro": 27, "North Beach": 6, "Embarcadero": 8,
        "Alamo Square": 21, "Nob Hill": 11, "Presidio": 17, "Mission District": 22, "Haight-Ashbury": 22
    },
    "Mission District": {
        "Union Square": 15, "The Castro": 7, "North Beach": 17, "Embarcadero": 19,
        "Alamo Square": 11, "Nob Hill": 12, "Presidio": 25, "Fisherman's Wharf": 22, "Haight-Ashbury": 12
    },
    "Haight-Ashbury": {
        "Union Square": 19, "The Castro": 6, "North Beach": 19, "Embarcadero": 20,
        "Alamo Square": 5, "Nob Hill": 15, "Presidio": 15, "Fisherman's Wharf": 23, "Mission District": 11
    }
}

friends = [
    {"name": "Melissa", "location": "The Castro", "start": time_str_to_minutes("20:15"), "end": time_str_to_minutes("21:15"), "duration": 30},
    {"name": "Kimberly", "location": "North Beach", "start": time_str_to_minutes("7:00"), "end": time_str_to_minutes("10:30"), "duration": 15},
    {"name": "Joseph", "location": "Embarcadero", "start": time_str_to_minutes("15:30"), "end": time_str_to_minutes("19:30"), "duration": 75},
    {"name": "Barbara", "location": "Alamo Square", "start": time_str_to_minutes("20:45"), "end": time_str_to_minutes("21:45"), "duration": 15},
    {"name": "Kenneth", "location": "Nob Hill", "start": time_str_to_minutes("12:15"), "end": time_str_to_minutes("17:15"), "duration": 105},
    {"name": "Joshua", "location": "Presidio", "start": time_str_to_minutes("16:30"), "end": time_str_to_minutes("18:15"), "duration": 105},
    {"name": "Brian", "location": "Fisherman's Wharf", "start": time_str_to_minutes("9:30"), "end": time_str_to_minutes("15:30"), "duration": 45},
    {"name": "Steven", "location": "Mission District", "start": time_str_to_minutes("19:30"), "end": time_str_to_minutes("21:00"), "duration": 90},
    {"name": "Betty", "location": "Haight-Ashbury", "start": time_str_to_minutes("19:00"), "end": time_str_to_minutes("20:30"), "duration": 90}
]

friends_dict = {f["name"]: f for f in friends}

base_order = ["Kimberly", "Brian", "Kenneth", "Joseph", "Joshua", "Betty", "Melissa", "Barbara"]
candidates = []

# Generate candidates by inserting Steven at every possible position
for i in range(len(base_order) + 1):
    candidate = base_order[:i] + ["Steven"] + base_order[i:]
    candidates.append(candidate)

# Add special candidate without Joshua, Betty, Melissa
candidates.append(["Kimberly", "Brian", "Kenneth", "Joseph", "Steven", "Barbara"])

best_itinerary = None
best_count = -1

start_time = 540  # 9:00 AM
start_location = "Union Square"

for candidate in candidates:
    current_time = start_time
    current_location = start_location
    itinerary = []
    
    for name in candidate:
        friend = friends_dict[name]
        travel_time = travel_times[current_location].get(friend["location"], 0)
        arrival = current_time + travel_time
        meeting_start = max(arrival, friend["start"])
        
        if meeting_start + friend["duration"] <= friend["end"]:
            meeting_end = meeting_start + friend["duration"]
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": name,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = friend["location"]
    
    # Check constraint: must meet at least one of Joshua or Steven
    met_names = {event["person"] for event in itinerary}
    if "Joshua" not in met_names and "Steven" not in met_names:
        continue
        
    count = len(itinerary)
    if count > best_count:
        best_count = count
        best_itinerary = itinerary

output = {"itinerary": best_itinerary}
print(json.dumps(output, indent=2))