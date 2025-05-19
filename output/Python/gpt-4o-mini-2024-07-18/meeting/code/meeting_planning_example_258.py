import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Richmond District", "Fisherman's Wharf"): 18
}

# Meeting constraints
meetings = {
    "Betty": {"location": "Presidio", "available_from": "10:15", "available_to": "21:30", "min_duration": 45},
    "David": {"location": "Richmond District", "available_from": "13:00", "available_to": "20:15", "min_duration": 90},
    "Barbara": {"location": "Fisherman's Wharf", "available_from": "09:15", "available_to": "20:15", "min_duration": 120},
}

# Arrival time
arriving_time = datetime.strptime("09:00", "%H:%M")

# Function to calculate potential meeting times
def calculate_meeting(person, start_time):
    available_start = datetime.strptime(meetings[person]["available_from"], "%H:%M")
    available_end = datetime.strptime(meetings[person]["available_to"], "%H:%M")
    min_duration = timedelta(minutes=meetings[person]["min_duration"])
    
    travel_time_to_location = travel_times[("Embarcadero", meetings[person]["location"])]
    travel_time = timedelta(minutes=travel_time_to_location)
    
    meeting_start = max(start_time + travel_time, available_start)
    meeting_end = meeting_start + min_duration
    
    if meeting_end <= available_end:
        return (meeting_start, meeting_end)
    return None

# Itinerary to hold the meetings
itinerary = []

# Compute the schedule
current_time = arriving_time
# Meeting Barbara first as she's available earliest after you arrive
barbara_meeting = calculate_meeting("Barbara", current_time)
if barbara_meeting:
    itinerary.append({
        "action": "meet",
        "location": "Fisherman's Wharf",
        "person": "Barbara",
        "start_time": barbara_meeting[0].strftime("%H:%M"),
        "end_time": barbara_meeting[1].strftime("%H:%M"),
    })
    current_time = barbara_meeting[1]

# After meeting Barbara, check for Betty
betty_meeting = calculate_meeting("Betty", current_time)
if betty_meeting:
    itinerary.append({
        "action": "meet",
        "location": "Presidio",
        "person": "Betty",
        "start_time": betty_meeting[0].strftime("%H:%M"),
        "end_time": betty_meeting[1].strftime("%H:%M"),
    })
    current_time = betty_meeting[1]

# Finally, check for David
david_meeting = calculate_meeting("David", current_time)
if david_meeting:
    itinerary.append({
        "action": "meet",
        "location": "Richmond District",
        "person": "David",
        "start_time": david_meeting[0].strftime("%H:%M"),
        "end_time": david_meeting[1].strftime("%H:%M"),
    })

# Output result as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))