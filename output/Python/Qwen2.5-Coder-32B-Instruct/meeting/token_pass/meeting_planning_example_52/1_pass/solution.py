import json
from datetime import datetime, timedelta

# Define input parameters
arrival_time_minutes = 540  # 9:00 AM in minutes
barbara_start_minutes = 795  # 1:15 PM in minutes
barbara_end_minutes = 990    # 6:15 PM in minutes
min_meeting_duration = 45    # 45 minutes
travel_to_richmond = 14      # 14 minutes
travel_to_russian_hill = 13  # 13 minutes

def minutes_to_time(minutes):
    return str(timedelta(minutes=minutes))[:-3]  # Converts minutes to H:MM format

# Calculate the earliest and latest possible departure times from Russian Hill
earliest_departure = barbara_start_minutes - min_meeting_duration - travel_to_richmond
latest_departure = barbara_end_minutes - min_meeting_duration - travel_to_richmond

# Check if a valid meeting time exists
if earliest_departure <= latest_departure:
    # Schedule the meeting at the earliest feasible time
    meeting_start = earliest_departure + travel_to_richmond
    meeting_end = meeting_start + min_meeting_duration
    
    itinerary = [
        {
            "action": "meet",
            "location": "Richmond District",
            "person": "Barbara",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
    ]
else:
    # No valid meeting time found
    itinerary = []

# Convert itinerary to JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))