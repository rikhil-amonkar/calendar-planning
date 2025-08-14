import json

def minutes_to_time(t):
    hours = t // 60
    minutes = t % 60
    return f"{hours}:{minutes:02d}"

# Input parameters
start_location = "Sunset District"
start_time_minutes = 9 * 60  # 9:00 AM in minutes
joshua_location = "Golden Gate Park"
joshua_available_start = 20 * 60 + 45  # 8:45 PM in 24h format
joshua_available_end = 21 * 60 + 45    # 9:45 PM in 24h format
min_meeting_duration = 15  # minutes
travel_sunset_to_ggp = 11  # minutes

# Calculate earliest possible meeting start time
meeting_start = joshua_available_start
meeting_end = meeting_start + min_meeting_duration

# Validate meeting fits within Joshua's availability window
if meeting_end <= joshua_available_end:
    # Calculate required departure time from Sunset District
    departure_time = meeting_start - travel_sunset_to_ggp
    
    # Ensure departure time is after arrival at Sunset District
    if departure_time >= start_time_minutes:
        itinerary = [{
            "action": "meet",
            "location": joshua_location,
            "person": "Joshua",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }]
        result = {"itinerary": itinerary}
    else:
        result = {"itinerary": []}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))