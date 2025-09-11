import json

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m}"

# Input parameters
user_start_location = "Alamo Square"
user_start_time = "9:00"  # Arrival at Alamo Square

# Timothy's constraints
timothy_location = "Richmond District"
timothy_available_start_time = "20:45"
timothy_available_end_time = "21:30"
min_meeting_duration = 45  # minutes

# Travel time from Alamo Square to Richmond District
travel_time_alamo_to_richmond = 12  # minutes

# Convert times to minutes
user_start_minutes = time_str_to_minutes(user_start_time)
timothy_available_start = time_str_to_minutes(timothy_available_start_time)
timothy_available_end = time_str_to_minutes(timothy_available_end_time)

# Calculate required arrival time at Richmond District
required_arrival_richmond = timothy_available_end - min_meeting_duration

# Calculate required departure from Alamo Square
required_departure_alamo = required_arrival_richmond - travel_time_alamo_to_richmond

itinerary = []
if required_departure_alamo >= user_start_minutes:
    # Meeting can happen
    meeting_start = timothy_available_start
    meeting_end = timothy_available_start + min_meeting_duration
    itinerary.append({
        "action": "meet",
        "location": timothy_location,
        "person": "Timothy",
        "start_time": minutes_to_time_str(meeting_start),
        "end_time": minutes_to_time_str(meeting_end)
    })

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))