import json
from datetime import datetime, timedelta

def convert_to_minutes(time_str):
    """Converts time in 'H:MM' format to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def convert_to_time(minutes):
    """Converts minutes since midnight to 'H:MM' format."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

def calculate_optimal_schedule():
    # Constants
    start_time_fishermans_wharf = "9:00"
    travel_time = 11  # in minutes
    kenneth_start = "14:15"  # 2:15 PM
    kenneth_end = "19:45"  # 7:45 PM
    min_meeting_duration = 90  # in minutes

    # Convert times to minutes since midnight
    start_minutes = convert_to_minutes(start_time_fishermans_wharf)
    kenneth_start_minutes = convert_to_minutes(kenneth_start)
    kenneth_end_minutes = convert_to_minutes(kenneth_end)

    # Calculate the latest time we can leave Fisherman's Wharf
    latest_leave_time = kenneth_end_minutes - min_meeting_duration - travel_time

    # Check if it's possible to meet Kenneth for the required duration
    if start_minutes + travel_time > latest_leave_time:
        # It's not possible to meet Kenneth for 90 minutes
        return {"itinerary": []}

    # Calculate the earliest time we can meet Kenneth
    earliest_meet_time = max(start_minutes + travel_time, kenneth_start_minutes)

    # Calculate the end time of the meeting
    meeting_end_time = earliest_meet_time + min_meeting_duration

    # Convert times back to HH:MM format
    start_meeting_time_str = convert_to_time(earliest_meet_time)
    end_meeting_time_str = convert_to_time(meeting_end_time)

    # Construct the itinerary
    itinerary = [
        {
            "action": "travel",
            "location": "Nob Hill",
            "start_time": convert_to_time(start_minutes),
            "end_time": convert_to_time(start_minutes + travel_time)
        },
        {
            "action": "meet",
            "location": "Nob Hill",
            "person": "Kenneth",
            "start_time": start_meeting_time_str,
            "end_time": end_meeting_time_str
        }
    ]

    return {"itinerary": itinerary}

# Generate and print the optimal schedule in JSON format
optimal_schedule = calculate_optimal_schedule()
print(json.dumps(optimal_schedule, indent=2))