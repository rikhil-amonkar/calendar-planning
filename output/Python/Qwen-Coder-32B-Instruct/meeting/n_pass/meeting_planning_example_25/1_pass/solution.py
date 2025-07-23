import json
from datetime import datetime, timedelta

# Input parameters
arrival_time = "9:00"
travel_time = 23  # in minutes
david_start_time = "16:00"
david_end_time = "21:45"
minimum_meeting_duration = 105  # in minutes

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes}" if hours > 9 else f"{hours}:{minutes:02}"

arrival_minutes = time_to_minutes(arrival_time)
david_start_minutes = time_to_minutes(david_start_time)
david_end_minutes = time_to_minutes(david_end_time)

# Calculate the latest possible start time for meeting David
latest_start_for_david = david_end_minutes - minimum_meeting_duration

# Determine if it's feasible to meet David
if latest_start_for_david < arrival_minutes + travel_time:
    itinerary = []
else:
    # Plan to meet David at the latest possible start time
    meeting_start = max(arrival_minutes + travel_time, david_start_minutes)
    meeting_end = meeting_start + minimum_meeting_duration
    
    itinerary = [
        {
            "action": "meet",
            "location": "Chinatown",
            "person": "David",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
    ]

result = {
    "itinerary": itinerary
}

print(json.dumps(result))