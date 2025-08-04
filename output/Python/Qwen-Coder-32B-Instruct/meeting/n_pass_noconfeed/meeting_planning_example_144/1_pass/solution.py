import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Financial District"): 20,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Financial District"): 17,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Mission District"): 17
}

# Define constraints
arrival_time = datetime.strptime("9:00", "%H:%M")
laura_start = datetime.strptime("12:15", "%H:%M")
laura_end = datetime.strptime("19:45", "%H:%M")
laura_min_meeting = 75
anthony_start = datetime.strptime("12:30", "%H:%M")
anthony_end = datetime.strptime("14:45", "%H:%M")
anthony_min_meeting = 30

def time_to_str(time):
    return time.strftime("%H:%M")

def find_meeting_time(start, end, min_duration):
    duration = end - start
    if duration.total_seconds() / 60 >= min_duration:
        return start, start + timedelta(minutes=min_duration)
    return None, None

def calculate_schedule():
    itinerary = []
    current_location = "The Castro"
    current_time = arrival_time

    # Try to meet Anthony first
    anthony_meeting_start, anthony_meeting_end = find_meeting_time(
        max(current_time + timedelta(minutes=travel_times[(current_location, "Financial District")]), anthony_start),
        anthony_end,
        anthony_min_meeting
    )
    if anthony_meeting_start:
        itinerary.append({
            "action": "meet",
            "location": "Financial District",
            "person": "Anthony",
            "start_time": time_to_str(anthony_meeting_start),
            "end_time": time_to_str(anthony_meeting_end)
        })
        current_time = anthony_meeting_end
        current_location = "Financial District"

    # Try to meet Laura
    laura_meeting_start, laura_meeting_end = find_meeting_time(
        max(current_time + timedelta(minutes=travel_times[(current_location, "Mission District")]), laura_start),
        laura_end,
        laura_min_meeting
    )
    if laura_meeting_start:
        itinerary.append({
            "action": "meet",
            "location": "Mission District",
            "person": "Laura",
            "start_time": time_to_str(laura_meeting_start),
            "end_time": time_to_str(laura_meeting_end)
        })

    return itinerary

schedule = calculate_schedule()
print(json.dumps({"itinerary": schedule}, indent=2))