import json
from datetime import datetime, timedelta

# Input parameters
arrival_time = datetime.strptime("9:00", "%H:%M")
travel_time = timedelta(minutes=7)
barbara_start = datetime.strptime("7:15", "%H:%M")
barbara_end = datetime.strptime("22:00", "%H:%M")
min_meeting_duration = timedelta(minutes=60)

def format_time(time):
    return time.strftime("%H:%M").lstrip('0')

def calculate_schedule():
    itinerary = []
    
    # Check if we can meet Barbara
    if arrival_time + min_meeting_duration <= barbara_end:
        meeting_start = max(arrival_time, barbara_start)
        meeting_end = meeting_start + min_meeting_duration
        
        itinerary.append({
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Barbara",
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end)
        })
    
    return itinerary

schedule = {
    "itinerary": calculate_schedule()
}

print(json.dumps(schedule))