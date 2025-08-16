import json
from datetime import datetime, timedelta

# Input parameters
arrival_time = datetime.strptime("9:00", "%H:%M")
travel_time = timedelta(minutes=7)
barbara_start = datetime.strptime("7:15", "%H:%M")
barbara_end = datetime.strptime("22:00", "%H:%M")
min_meeting_duration = timedelta(minutes=60)

def format_time(time):
    return time.strftime("%H:%M")

def calculate_schedule():
    itinerary = []
    
    # Calculate the earliest possible meeting start time after accounting for travel time
    earliest_meeting_start = arrival_time + travel_time
    
    # Check if we can meet Barbara
    if earliest_meeting_start + min_meeting_duration <= barbara_end:
        meeting_start = max(earliest_meeting_start, barbara_start)
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