import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

# Input parameters
start_location = "Russian Hill"
start_time_str = "9:00"
barbara_available_start = "7:15"
barbara_available_end = "22:00"
min_meeting_duration = 60
travel_time = 7

# Convert times to minutes since midnight
start_time_minutes = time_to_minutes(start_time_str)
barbara_start_minutes = time_to_minutes(barbara_available_start)
barbara_end_minutes = time_to_minutes(barbara_available_end)

# Calculate earliest arrival at Pacific Heights
earliest_arrival = start_time_minutes + travel_time

# Determine meeting start time (must be after arrival and during availability)
meeting_start = max(earliest_arrival, barbara_start_minutes)
meeting_end = meeting_start + min_meeting_duration

# Check if meeting fits within Barbara's availability
if meeting_end <= barbara_end_minutes:
    meeting_start_time = minutes_to_time(meeting_start)
    meeting_end_time = minutes_to_time(meeting_end)
    itinerary = [
        {
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Barbara",
            "start_time": meeting_start_time,
            "end_time": meeting_end_time
        }
    ]
else:
    itinerary = []

# Output result as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))