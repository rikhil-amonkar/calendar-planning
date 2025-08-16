import json
from datetime import datetime, timedelta

def calculate_meeting_schedule():
    # Input parameters
    start_time = datetime.strptime("9:00", "%H:%M")
    travel_nob_to_presidio = timedelta(minutes=17)
    travel_presidio_to_nob = timedelta(minutes=18)
    robert_start = datetime.strptime("11:15", "%H:%M")
    robert_end = datetime.strptime("17:45", "%H:%M")
    min_meeting_duration = timedelta(minutes=120)

    # Calculate the earliest possible meeting time with Robert
    meeting_start = max(start_time + travel_nob_to_presidio, robert_start)
    meeting_end = meeting_start + min_meeting_duration

    # Check if the calculated meeting end time is within Robert's availability
    if meeting_end <= robert_end:
        itinerary = [
            {
                "action": "meet",
                "location": "Presidio",
                "person": "Robert",
                "start_time": meeting_start.strftime("%H:%M"),
                "end_time": meeting_end.strftime("%H:%M")
            }
        ]
    else:
        itinerary = []

    return json.dumps({"itinerary": itinerary}, indent=2)

print(calculate_meeting_schedule())