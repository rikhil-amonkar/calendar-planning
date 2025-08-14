import json

def to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
start_location = "Golden Gate Park"
start_time = to_minutes("9:00")  # 540 minutes since midnight

# Travel times (in minutes)
travel_ggp_chinatown = 23

# David's availability
david_location = "Chinatown"
david_start_time = to_minutes("16:00")  # 960 minutes since midnight
david_end_time = to_minutes("21:45")    # 1305 minutes since midnight

# Meeting duration requirement
min_meeting_duration = 105

# Compute latest possible start time for meeting with David
latest_meeting_start = david_end_time - min_meeting_duration

# Check if it's within David's availability
itinerary = []
if latest_meeting_start >= david_start_time:
    # Calculate required departure time from Golden Gate Park
    required_departure = latest_meeting_start - travel_ggp_chinatown
    
    # Ensure departure time is after arrival at start location
    if required_departure >= start_time:
        meeting_start = latest_meeting_start
        meeting_end = meeting_start + min_meeting_duration
        itinerary.append({
            "action": "meet",
            "location": david_location,
            "person": "David",
            "start_time": to_time_str(meeting_start),
            "end_time": to_time_str(meeting_end)
        })

result = {"itinerary": itinerary}
print(json.dumps(result))