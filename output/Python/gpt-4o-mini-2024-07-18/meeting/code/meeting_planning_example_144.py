import json
from datetime import datetime, timedelta

# Constants
TRAVEL_TIMES = {
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Financial District"): 20,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Financial District"): 17,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Mission District"): 17,
}

# Meeting constraints
arrival_time = datetime.strptime("09:00", "%H:%M")
laura_start = datetime.strptime("12:15", "%H:%M")
laura_end = datetime.strptime("19:45", "%H:%M")
anthony_start = datetime.strptime("12:30", "%H:%M")
anthony_end = datetime.strptime("14:45", "%H:%M")
laura_meeting_duration = timedelta(minutes=75)
anthony_meeting_duration = timedelta(minutes=30)

# Initialize meeting schedule
itinerary = []

# Define a function to add meetings to the itinerary
def add_meeting(location, person, start_time, duration):
    end_time = start_time + duration
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": start_time.strftime("%H:%M"),
        "end_time": end_time.strftime("%H:%M"),
    })
    return end_time

# Meeting with Anthony
# From Castro to Financial District
travel_to_anthony = TRAVEL_TIMES[("The Castro", "Financial District")]
time_after_travel_to_anthony = arrival_time + timedelta(minutes=travel_to_anthony)

if time_after_travel_to_anthony <= anthony_start:
    start_time_anthony = anthony_start
else:
    start_time_anthony = time_after_travel_to_anthony

end_time_anthony = start_time_anthony + anthony_meeting_duration

# Ensure the meeting with Anthony ends before he leaves
if end_time_anthony > anthony_end:
    end_time_anthony = anthony_end
    start_time_anthony = end_time_anthony - anthony_meeting_duration

add_meeting("Financial District", "Anthony", start_time_anthony, anthony_meeting_duration)

# Travel back to Castro or to Mission District directly
if end_time_anthony < laura_start:
    travel_to_castro = TRAVEL_TIMES[("Financial District", "The Castro")]
    end_time_anthony += timedelta(minutes=travel_to_castro)

# Meeting with Laura
# From Castro to Mission District
travel_to_laura = TRAVEL_TIMES[("The Castro", "Mission District")]
start_time_laura = end_time_anthony + timedelta(minutes=travel_to_laura)

if start_time_laura < laura_start:
    start_time_laura = laura_start

end_time_laura = start_time_laura + laura_meeting_duration

# Ensure the meeting with Laura ends before she leaves
if end_time_laura > laura_end:
    end_time_laura = laura_end
    start_time_laura = end_time_laura - laura_meeting_duration

add_meeting("Mission District", "Laura", start_time_laura, laura_meeting_duration)

# Generate output
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))