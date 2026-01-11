import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert time in 'H:MM' format to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time in 'H:MM' format."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

def calculate_meeting_schedule():
    # Constants
    arrival_time = "9:00"
    barbara_start = "7:15"
    barbara_end = "22:00"  # 10:00 PM in 24-hour format
    meeting_duration = 60  # in minutes
    travel_time = 7  # in minutes
    
    # Convert times to minutes
    arrival_minutes = time_to_minutes(arrival_time)
    barbara_start_minutes = time_to_minutes(barbara_start)
    barbara_end_minutes = time_to_minutes(barbara_end)
    
    # Calculate the earliest and latest possible meeting start times
    earliest_meeting_start = max(arrival_minutes + travel_time, barbara_start_minutes)
    latest_meeting_start = barbara_end_minutes - meeting_duration
    
    # Check if a valid meeting window exists
    if earliest_meeting_start > latest_meeting_start:
        return {"itinerary": []}  # No valid meeting window
    
    # Choose the earliest possible meeting start time
    meeting_start = earliest_meeting_start
    meeting_end = meeting_start + meeting_duration
    
    # Create the itinerary
    itinerary = [
        {
            "action": "travel",
            "location": "Pacific Heights",
            "start_time": arrival_time,
            "end_time": minutes_to_time(arrival_minutes + travel_time)
        },
        {
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Barbara",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
    ]
    
    return {"itinerary": itinerary}

# Generate and print the schedule
schedule = calculate_meeting_schedule()
print(json.dumps(schedule, indent=2))