import json

def time_to_minutes(time_str):
    parts = time_str.replace('AM', '').replace('PM', '').split(':')
    hour = int(parts[0])
    minute = int(parts[1]) if len(parts) > 1 else 0
    if "PM" in time_str and hour != 12:
        hour += 12
    if "AM" in time_str and hour == 12:
        hour = 0
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Input parameters
start_location = "Fisherman's Wharf"
start_time_str = "9:00AM"
kenneth_location = "Nob Hill"
kenneth_available_start_str = "2:15PM"
kenneth_available_end_str = "7:45PM"
min_meeting_duration = 90

travel_times = {
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Nob Hill", "Fisherman's Wharf"): 11
}

# Convert times to minutes
start_minutes = time_to_minutes(start_time_str)
kenneth_start = time_to_minutes(kenneth_available_start_str)
kenneth_end = time_to_minutes(kenneth_available_end_str)
travel_time = travel_times[(start_location, kenneth_location)]

# Calculate earliest possible meeting start at Nob Hill
earliest_arrival = start_minutes + travel_time
meeting_start = max(earliest_arrival, kenneth_start)
meeting_end = meeting_start + min_meeting_duration

# Check if meeting fits in Kenneth's availability
if meeting_end > kenneth_end:
    meeting_start = kenneth_end - min_meeting_duration
    meeting_end = kenneth_end
    if meeting_start < kenneth_start:
        itinerary = []
    else:
        itinerary = [{
            "action": "meet",
            "location": kenneth_location,
            "person": "Kenneth",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }]
else:
    itinerary = [{
        "action": "meet",
        "location": kenneth_location,
        "person": "Kenneth",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    }]

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))