import json

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
travel_to_park = 11
travel_from_park = 10
start_location = "Sunset District"
start_time = "9:00"
joshua_location = "Golden Gate Park"
joshua_window_start = "20:45"
joshua_window_end = "21:45"
min_meeting_duration = 15

# Convert times to minutes
start_minutes = time_to_minutes(start_time)
joshua_start_minutes = time_to_minutes(joshua_window_start)
joshua_end_minutes = time_to_minutes(joshua_window_end)

# Calculate latest departure time from Sunset to meet Joshua
latest_departure_time = joshua_start_minutes - travel_to_park

# Calculate meeting window
meeting_start = max(joshua_start_minutes, latest_departure_time + travel_to_park)
meeting_end = joshua_end_minutes
meeting_duration = meeting_end - meeting_start

# Ensure minimum meeting duration
if meeting_duration < min_meeting_duration:
    # Adjust meeting start to ensure minimum duration
    meeting_start = joshua_end_minutes - min_meeting_duration
    # Check if we can arrive in time
    if meeting_start - travel_to_park < start_minutes:
        meeting_start = start_minutes + travel_to_park
        meeting_end = meeting_start + min_meeting_duration
    else:
        meeting_end = joshua_end_minutes

# Convert back to time strings
meeting_start_str = minutes_to_time(meeting_start)
meeting_end_str = minutes_to_time(meeting_end)

# Create itinerary
itinerary = [
    {
        "action": "meet",
        "location": joshua_location,
        "person": "Joshua",
        "start_time": meeting_start_str,
        "end_time": meeting_end_str
    }
]

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))