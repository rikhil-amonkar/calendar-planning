import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Golden Gate Park"): 23,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Chinatown"): 23,
}

# Meeting constraints
arrival_time = datetime.strptime("09:00", "%H:%M")
kenneth_start = datetime.strptime("12:00", "%H:%M")
kenneth_end = datetime.strptime("15:00", "%H:%M")
barbara_start = datetime.strptime("08:15", "%H:%M")
barbara_end = datetime.strptime("19:00", "%H:%M")

# Meeting duration requirements
kenneth_meet_duration = timedelta(minutes=90)
barbara_meet_duration = timedelta(minutes=45)

# Schedule
itinerary = []

# Helper function to schedule a meeting
def schedule_meeting(person, location, start_time, duration):
    end_time = start_time + duration
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": start_time.strftime("%H:%M"),
        "end_time": end_time.strftime("%H:%M"),
    })
    return end_time

# Visit Barbara first
# Travel from Financial District to Golden Gate Park
departure_time = arrival_time + timedelta(minutes=travel_times[("Financial District", "Golden Gate Park")])
if departure_time < barbara_start:
    departure_time = barbara_start

# Meeting with Barbara
end_time_barbara = schedule_meeting("Barbara", "Golden Gate Park", departure_time, barbara_meet_duration)

# After meeting Barbara, travel to Chinatown
# Travel from Golden Gate Park to Chinatown
departure_time = end_time_barbara + timedelta(minutes=travel_times[("Golden Gate Park", "Chinatown")])

# Meeting with Kenneth
if departure_time < kenneth_start:
    departure_time = kenneth_start
end_time_kenneth = schedule_meeting("Kenneth", "Chinatown", departure_time, kenneth_meet_duration)

# Convert the itinerary to JSON format
output = {
    "itinerary": itinerary
}

# Print the JSON output
print(json.dumps(output, indent=2))