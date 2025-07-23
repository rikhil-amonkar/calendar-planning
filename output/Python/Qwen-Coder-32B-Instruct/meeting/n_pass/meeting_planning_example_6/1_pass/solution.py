import json
from datetime import datetime, timedelta

# Input parameters
arrival_time = datetime.strptime('9:00', '%H:%M')
fisher_to_nob_hill_travel_time = timedelta(minutes=11)
nob_hill_to_fisher_travel_time = timedelta(minutes=11)
kenneth_start_time = datetime.strptime('14:15', '%H:%M')
kenneth_end_time = datetime.strptime('19:45', '%H:%M')
minimum_meeting_duration = timedelta(minutes=90)

def format_time(time):
    return time.strftime('%H:%M')

def calculate_schedule():
    itinerary = []
    
    # Start at Fisherman's Wharf
    current_time = arrival_time
    
    # Travel to Nob Hill
    travel_to_nob_hill_time = current_time + fisher_to_nob_hill_travel_time
    if travel_to_nob_hill_time < kenneth_start_time:
        current_time = travel_to_nob_hill_time
    else:
        # If we can't make it to Nob Hill before Kenneth arrives, skip the trip
        return {"itinerary": itinerary}
    
    # Meet Kenneth at Nob Hill
    meeting_start_time = max(current_time, kenneth_start_time)
    meeting_end_time = min(meeting_start_time + minimum_meeting_duration, kenneth_end_time)
    
    if meeting_end_time - meeting_start_time >= minimum_meeting_duration:
        itinerary.append({
            "action": "meet",
            "location": "Nob Hill",
            "person": "Kenneth",
            "start_time": format_time(meeting_start_time),
            "end_time": format_time(meeting_end_time)
        })
    
    return {"itinerary": itinerary}

schedule = calculate_schedule()
print(json.dumps(schedule))