import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
start_time_str = "9:00"
robert_available_start_str = "11:15"
robert_available_end_str = "17:45"
min_duration = 120
travel_time = 17  # Nob Hill to Presidio

# Convert times to minutes
start_minutes = time_to_minutes(start_time_str)
available_start_minutes = time_to_minutes(robert_available_start_str)
available_end_minutes = time_to_minutes(robert_available_end_str)

# Calculate earliest possible meeting start
arrival_time = start_minutes + travel_time
meeting_start_minutes = max(available_start_minutes, arrival_time)
meeting_end_minutes = meeting_start_minutes + min_duration

# Check if meeting is possible
if meeting_end_minutes <= available_end_minutes:
    meeting_start = minutes_to_time(meeting_start_minutes)
    meeting_end = minutes_to_time(meeting_end_minutes)
    itinerary = [
        {
            "action": "meet",
            "location": "Presidio",
            "person": "Robert",
            "start_time": meeting_start,
            "end_time": meeting_end
        }
    ]
else:
    itinerary = []

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))