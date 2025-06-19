import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Input parameters
start_location = "Alamo Square"
start_time_str = "9:00"
timothy_location = "Richmond District"
timothy_start_str = "20:45"
timothy_end_str = "21:30"
min_duration = 45
travel_time_to_richmond = 12

# Convert times to minutes
start_minutes = time_to_minutes(start_time_str)
timothy_start_min = time_to_minutes(timothy_start_str)
timothy_end_min = time_to_minutes(timothy_end_str)

# Calculate meeting parameters
available_duration = timothy_end_min - timothy_start_min
departure_time = timothy_start_min - travel_time_to_richmond

# Initialize itinerary
itinerary = []

# Check if meeting is feasible
if available_duration >= min_duration and departure_time >= start_minutes:
    meeting_start = timothy_start_min
    meeting_end = timothy_end_min
    itinerary.append({
        "action": "meet",
        "location": timothy_location,
        "person": "Timothy",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })

# Output result as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))