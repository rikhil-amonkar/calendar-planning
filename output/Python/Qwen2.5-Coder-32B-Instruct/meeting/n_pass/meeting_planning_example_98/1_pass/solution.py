import json
from datetime import datetime, timedelta

# Input parameters
arrival_time = "9:00"
timothy_start = "20:45"
timothy_end = "21:30"
min_meeting_duration = 45  # in minutes
travel_time_to_richmond = 12  # in minutes
travel_time_to_alamosquare = 13  # in minutes

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M").lstrip('0')

def calculate_optimal_schedule(arrival_time, timothy_start, timothy_end, min_meeting_duration, travel_time_to_richmond, travel_time_to_alamosquare):
    arrival_time = parse_time(arrival_time)
    timothy_start = parse_time(timothy_start)
    timothy_end = parse_time(timothy_end)

    # Calculate the latest time we can leave Alamo Square to still meet Timothy for the required duration
    latest_leave_time = timothy_end - timedelta(minutes=min_meeting_duration + travel_time_to_richmond)

    if arrival_time > latest_leave_time:
        # Not enough time to travel to Richmond and meet Timothy for the required duration
        return {"itinerary": []}

    # Schedule the meeting with Timothy
    meeting_start_time = max(arrival_time + timedelta(minutes=travel_time_to_richmond), timothy_start)
    meeting_end_time = meeting_start_time + timedelta(minutes=min_meeting_duration)

    itinerary = [
        {
            "action": "meet",
            "location": "Richmond District",
            "person": "Timothy",
            "start_time": format_time(meeting_start_time),
            "end_time": format_time(meeting_end_time)
        }
    ]

    return {"itinerary": itinerary}

schedule = calculate_optimal_schedule(arrival_time, timothy_start, timothy_end, min_meeting_duration, travel_time_to_richmond, travel_time_to_alamosquare)
print(json.dumps(schedule))