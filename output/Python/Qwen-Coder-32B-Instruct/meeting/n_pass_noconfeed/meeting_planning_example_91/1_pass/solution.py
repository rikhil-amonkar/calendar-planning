import json
from datetime import datetime, timedelta

# Input parameters
arrival_time = "9:00"
travel_time_russian_to_richmond = 14
travel_time_richmond_to_russian = 13
daniel_start_time = "19:00"
daniel_end_time = "20:15"
minimum_meeting_duration_with_daniel = 75

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes}" if hours > 9 else f"{hours}:{minutes:02}"

def calculate_schedule():
    current_time = time_to_minutes(arrival_time)
    itinerary = []

    # Convert Daniel's availability to minutes
    daniel_start = time_to_minutes(daniel_start_time)
    daniel_end = time_to_minutes(daniel_end_time)

    # Check if we can meet Daniel
    if current_time + travel_time_russian_to_richmond <= daniel_start:
        travel_end_time = current_time + travel_time_russian_to_richmond
        meeting_start_time = max(travel_end_time, daniel_start)
        meeting_end_time = min(meeting_start_time + minimum_meeting_duration_with_daniel, daniel_end)

        if meeting_end_time - meeting_start_time >= minimum_meeting_duration_with_daniel:
            itinerary.append({
                "action": "meet",
                "location": "Richmond District",
                "person": "Daniel",
                "start_time": minutes_to_time(meeting_start_time),
                "end_time": minutes_to_time(meeting_end_time)
            })
            current_time = meeting_end_time + travel_time_richmond_to_russian
        else:
            # Not enough time to meet Daniel for the required duration
            pass

    return itinerary

itinerary = calculate_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))