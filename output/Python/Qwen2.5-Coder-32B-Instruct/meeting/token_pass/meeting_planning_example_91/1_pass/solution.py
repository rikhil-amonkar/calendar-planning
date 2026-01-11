import json
from datetime import datetime, timedelta

# Constants
START_LOCATION = "Russian Hill"
START_TIME = "9:00"  # in 24-hour format
TRAVEL_TIME_RUSSIAN_TO_RICHMOND = 14  # in minutes
TRAVEL_TIME_RICHMOND_TO_RUSSIAN = 13  # in minutes
DANIEL_START_TIME = "19:00"  # 7:00 PM
DANIEL_END_TIME = "20:15"  # 8:15 PM
MIN_MEETING_DURATION = 75  # in minutes

def time_to_minutes(time_str):
    """Converts time in 'H:MM' format to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes since midnight to 'H:MM' format."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

def generate_schedule():
    start_time_minutes = time_to_minutes(START_TIME)
    daniel_start_time_minutes = time_to_minutes(DANIEL_START_TIME)
    daniel_end_time_minutes = time_to_minutes(DANIEL_END_TIME)
    
    # Calculate the latest time we can leave Russian Hill to reach Richmond by Daniel's start time
    latest_leave_time_minutes = daniel_start_time_minutes - TRAVEL_TIME_RUSSIAN_TO_RICHMOND
    
    # Check if we can reach Richmond by Daniel's start time and stay for at least 75 minutes
    if start_time_minutes <= latest_leave_time_minutes:
        # Calculate the meeting end time
        meeting_end_time_minutes = min(daniel_end_time_minutes, daniel_start_time_minutes + MIN_MEETING_DURATION)
        
        # Create the itinerary
        itinerary = [
            {
                "action": "travel",
                "location": "Richmond District",
                "start_time": minutes_to_time(start_time_minutes),
                "end_time": minutes_to_time(start_time_minutes + TRAVEL_TIME_RUSSIAN_TO_RICHMOND)
            },
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Daniel",
                "start_time": minutes_to_time(start_time_minutes + TRAVEL_TIME_RUSSIAN_TO_RICHMOND),
                "end_time": minutes_to_time(meeting_end_time_minutes)
            }
        ]
    else:
        # If we can't reach in time, the itinerary is empty
        itinerary = []
    
    return {"itinerary": itinerary}

# Generate and print the schedule in JSON format
schedule = generate_schedule()
print(json.dumps(schedule, indent=2))