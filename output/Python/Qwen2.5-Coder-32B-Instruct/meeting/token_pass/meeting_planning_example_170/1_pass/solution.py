import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Russian Hill'): 4,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Russian Hill'): 13,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Union Square'): 11
}

# Define constraints
arrival_time = datetime.strptime('9:00', '%H:%M')
emily_start = datetime.strptime('16:00', '%H:%M')
emily_end = datetime.strptime('17:15', '%H:%M')
emily_min_meeting = timedelta(minutes=45)

margaret_start = datetime.strptime('19:00', '%H:%M')
margaret_end = datetime.strptime('21:00', '%H:%M')
margaret_min_meeting = timedelta(minutes=120)

def can_meet(start_time, end_time, min_duration):
    return (end_time - start_time) >= min_duration

def format_time(time):
    return time.strftime('%H:%M')

# Function to calculate the latest possible meeting time with Emily
def find_latest_emily_meeting():
    latest_start = emily_end - emily_min_meeting
    if latest_start >= arrival_time + travel_times[('North Beach', 'Union Square')]:
        return latest_start
    return None

# Function to calculate the latest possible meeting time with Margaret
def find_latest_margaret_meeting(emily_meeting_end=None):
    latest_start = margaret_end - margaret_min_meeting
    if latest_start >= arrival_time + travel_times[('North Beach', 'Russian Hill')]:
        return latest_start
    if emily_meeting_end:
        latest_start = margaret_end - margaret_min_meeting
        if latest_start >= emily_meeting_end + travel_times[('Union Square', 'Russian Hill')]:
            return latest_start
    return None

# Find the latest possible meeting times
emily_meeting_start = find_latest_emily_meeting()
margaret_meeting_start = find_latest_margaret_meeting(emily_meeting_start)

# Prepare the itinerary
itinerary = []
if emily_meeting_start:
    emily_meeting_end = emily_meeting_start + emily_min_meeting
    itinerary.append({
        "action": "meet",
        "location": "Union Square",
        "person": "Emily",
        "start_time": format_time(emily_meeting_start),
        "end_time": format_time(emily_meeting_end)
    })

if margaret_meeting_start:
    margaret_meeting_end = margaret_meeting_start + margaret_min_meeting
    itinerary.append({
        "action": "meet",
        "location": "Russian Hill",
        "person": "Margaret",
        "start_time": format_time(margaret_meeting_start),
        "end_time": format_time(margaret_meeting_end)
    })

# Output the result as a JSON-formatted dictionary
result = {
    "itinerary": itinerary
}

print(json.dumps(result, indent=2))