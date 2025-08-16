import json
from datetime import datetime, timedelta

# Input parameters
arrival_time = datetime.strptime('9:00', '%H:%M')
travel_time_nob_to_presidio = timedelta(minutes=17)
travel_time_presidio_to_nob = timedelta(minutes=18)
robert_start_time = datetime.strptime('11:15', '%H:%M')
robert_end_time = datetime.strptime('17:45', '%H:%M')
minimum_meeting_duration = timedelta(minutes=120)

def format_time(time):
    return time.strftime('%-H:%M')

def calculate_schedule():
    itinerary = []
    
    # Travel to Presidio
    current_time = arrival_time + travel_time_nob_to_presidio
    
    # Adjust meeting time if we arrive before Robert's availability
    if current_time < robert_start_time:
        current_time = robert_start_time
    
    # Calculate the end time of the meeting
    meeting_end_time = current_time + minimum_meeting_duration
    
    # Ensure the meeting does not exceed Robert's availability
    if meeting_end_time > robert_end_time:
        meeting_end_time = robert_end_time
        current_time = meeting_end_time - minimum_meeting_duration
    
    # Add meeting to itinerary
    itinerary.append({
        "action": "meet",
        "location": "Presidio",
        "person": "Robert",
        "start_time": format_time(current_time),
        "end_time": format_time(meeting_end_time)
    })
    
    return itinerary

schedule = calculate_schedule()
result = {
    "itinerary": schedule
}

print(json.dumps(result))