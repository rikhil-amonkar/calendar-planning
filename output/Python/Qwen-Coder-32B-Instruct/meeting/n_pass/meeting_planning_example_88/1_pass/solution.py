import json
from datetime import datetime, timedelta

# Input parameters
arrival_time = datetime.strptime("9:00", "%H:%M")
travel_time_sd_to_ggp = timedelta(minutes=11)
travel_time_ggp_to_sd = timedelta(minutes=10)
joshua_start_time = datetime.strptime("20:45", "%H:%M")
joshua_end_time = datetime.strptime("21:45", "%H:%M")
minimum_meeting_duration = timedelta(minutes=15)

def format_time(time):
    return time.strftime("%H:%M").lstrip('0')

def calculate_schedule():
    itinerary = []
    
    # Meeting with Joshua
    if joshua_end_time - joshua_start_time >= minimum_meeting_duration:
        meeting_start = joshua_start_time
        meeting_end = meeting_start + minimum_meeting_duration
        itinerary.append({
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Joshua",
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end)
        })
    
    return itinerary

schedule = calculate_schedule()
result = {
    "itinerary": schedule
}

print(json.dumps(result))