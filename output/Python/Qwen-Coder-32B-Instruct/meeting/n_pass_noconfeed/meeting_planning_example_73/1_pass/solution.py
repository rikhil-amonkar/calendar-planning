import json
from datetime import datetime, timedelta

# Input parameters
arrival_time = "9:00"
barbara_start = "7:15"
barbara_end = "22:00"
min_meeting_duration = 60
travel_time = 7  # in minutes

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

def calculate_schedule():
    arrival_minutes = time_to_minutes(arrival_time)
    barbara_start_minutes = time_to_minutes(barbara_start)
    barbara_end_minutes = time_to_minutes(barbara_end)

    # Calculate the earliest possible meeting start time with Barbara
    meeting_start = max(arrival_minutes, barbara_start_minutes)
    meeting_end = meeting_start + min_meeting_duration

    # Check if the meeting can end before Barbara leaves
    if meeting_end <= barbara_end_minutes:
        itinerary = [
            {
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Barbara",
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
        ]
    else:
        # If we can't meet Barbara for the full duration, adjust the meeting end time
        meeting_end = barbara_end_minutes
        meeting_start = meeting_end - min_meeting_duration

        # Check if we can still meet Barbara for the full duration after adjusting
        if meeting_start >= arrival_minutes and meeting_end <= barbara_end_minutes:
            itinerary = [
                {
                    "action": "meet",
                    "location": "Pacific Heights",
                    "person": "Barbara",
                    "start_time": minutes_to_time(meeting_start),
                    "end_time": minutes_to_time(meeting_end)
                }
            ]
        else:
            # If no valid meeting time is found, return an empty itinerary
            itinerary = []

    return itinerary

schedule = calculate_schedule()
output = {"itinerary": schedule}
print(json.dumps(output))