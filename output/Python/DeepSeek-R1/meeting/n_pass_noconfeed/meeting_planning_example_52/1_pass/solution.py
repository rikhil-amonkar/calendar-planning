import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1]) if len(parts) > 1 else 0
    return hour * 60 + minute

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
start_location = "Russian Hill"
start_time_str = "9:00"
barbara_available_start_str = "13:15"
barbara_available_end_str = "18:15"
min_meeting_duration = 45

# Travel times dictionary
travel_times = {
    ("Russian Hill", "Richmond District"): 14,
    ("Richmond District", "Russian Hill"): 13
}

# Convert times to minutes
start_time_minutes = time_to_minutes(start_time_str)
barbara_start_minutes = time_to_minutes(barbara_available_start_str)
barbara_end_minutes = time_to_minutes(barbara_available_end_str)

# Get travel time to Richmond District
travel_time = travel_times[(start_location, "Richmond District")]

# Calculate earliest possible arrival at Richmond District
earliest_arrival = start_time_minutes + travel_time

# Determine meeting start time
if earliest_arrival > barbara_start_minutes:
    meeting_start = earliest_arrival
else:
    meeting_start = barbara_start_minutes

# Ensure meeting fits within Barbara's availability
meeting_end = meeting_start + min_meeting_duration
if meeting_end > barbara_end_minutes:
    meeting_start = barbara_end_minutes - min_meeting_duration
    meeting_end = barbara_end_minutes

# Create meeting entry
itinerary = [
    {
        "action": "meet",
        "location": "Richmond District",
        "person": "Barbara",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    }
]

# Output result as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))