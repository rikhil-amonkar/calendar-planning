import json
from datetime import datetime, timedelta

# Define the travel times (in minutes)
travel_times = {
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Financial District"): 5,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Financial District"): 26,
    ("Haight-Ashbury", "Bayview"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Financial District"): 19,
    ("Presidio", "Financial District"): 22,
}

# Meeting Constraints
constraints = {
    "Mary": {
        "location": "Golden Gate Park",
        "available_from": "08:45",
        "available_to": "11:45",
        "min_meeting_time": 45
    },
    "Kevin": {
        "location": "Haight-Ashbury",
        "available_from": "10:15",
        "available_to": "16:15",
        "min_meeting_time": 90
    },
    "Deborah": {
        "location": "Bayview",
        "available_from": "15:00",
        "available_to": "19:15",
        "min_meeting_time": 120
    },
    "Stephanie": {
        "location": "Presidio",
        "available_from": "10:00",
        "available_to": "17:15",
        "min_meeting_time": 120
    },
    "Emily": {
        "location": "Financial District",
        "available_from": "11:30",
        "available_to": "21:45",
        "min_meeting_time": 105
    },
}

# Arrival time at Embarcadero
arrival_time = datetime.strptime("09:00", "%H:%M")

# Convert available time strings to datetime objects
for key, value in constraints.items():
    value["available_from"] = datetime.strptime(value["available_from"], "%H:%M")
    value["available_to"] = datetime.strptime(value["available_to"], "%H:%M")

# Initialize the itinerary
itinerary = []
current_time = arrival_time

# Function to calculate end time after travel and meeting
def add_meeting(start_time, duration):
    return start_time + timedelta(minutes=duration)

# Meeting Mary
if current_time <= constraints["Mary"]["available_to"] and current_time + timedelta(minutes=travel_times[("Embarcadero", "Golden Gate Park")]) <= constraints["Mary"]["available_from"]:
    travel_time = travel_times[("Embarcadero", "Golden Gate Park")]
    current_time = add_meeting(current_time, travel_time)  # Travel to Golden Gate Park
    meeting_start = add_meeting(current_time, 0)  # Start meeting right after arrival
    meeting_end = add_meeting(meeting_start, constraints["Mary"]["min_meeting_time"])
    itinerary.append({"action": "meet", "location": "Golden Gate Park", "person": "Mary", "start_time": meeting_start.strftime("%H:%M"), "end_time": meeting_end.strftime("%H:%M")})
    current_time = meeting_end  # Update current time after meeting

# Meeting Kevin
if current_time <= constraints["Kevin"]["available_to"]:
    travel_time = travel_times[("Golden Gate Park", "Haight-Ashbury")]
    current_time = add_meeting(current_time, travel_time)  # Travel to Haight-Ashbury
    meeting_start = max(current_time, constraints["Kevin"]["available_from"])
    meeting_end = add_meeting(meeting_start, constraints["Kevin"]["min_meeting_time"])
    itinerary.append({"action": "meet", "location": "Haight-Ashbury", "person": "Kevin", "start_time": meeting_start.strftime("%H:%M"), "end_time": meeting_end.strftime("%H:%M")})
    current_time = meeting_end  # Update current time after meeting

# Meeting Stephanie
if current_time <= constraints["Stephanie"]["available_to"]:
    travel_time = travel_times[("Haight-Ashbury", "Presidio")]
    current_time = add_meeting(current_time, travel_time)  # Travel to Presidio
    meeting_start = max(current_time, constraints["Stephanie"]["available_from"])
    meeting_end = add_meeting(meeting_start, constraints["Stephanie"]["min_meeting_time"])
    itinerary.append({"action": "meet", "location": "Presidio", "person": "Stephanie", "start_time": meeting_start.strftime("%H:%M"), "end_time": meeting_end.strftime("%H:%M")})
    current_time = meeting_end  # Update current time after meeting

# Meeting Deborah
if current_time <= constraints["Deborah"]["available_to"]:
    travel_time = travel_times[("Presidio", "Bayview")]
    current_time = add_meeting(current_time, travel_time)  # Travel to Bayview
    meeting_start = max(current_time, constraints["Deborah"]["available_from"])
    meeting_end = add_meeting(meeting_start, constraints["Deborah"]["min_meeting_time"])
    itinerary.append({"action": "meet", "location": "Bayview", "person": "Deborah", "start_time": meeting_start.strftime("%H:%M"), "end_time": meeting_end.strftime("%H:%M")})
    current_time = meeting_end  # Update current time after meeting

# Meeting Emily
if current_time <= constraints["Emily"]["available_to"]:
    travel_time = travel_times[("Bayview", "Financial District")]
    current_time = add_meeting(current_time, travel_time)  # Travel to Financial District
    meeting_start = max(current_time, constraints["Emily"]["available_from"])
    meeting_end = add_meeting(meeting_start, constraints["Emily"]["min_meeting_time"])
    itinerary.append({"action": "meet", "location": "Financial District", "person": "Emily", "start_time": meeting_start.strftime("%H:%M"), "end_time": meeting_end.strftime("%H:%M")})
    current_time = meeting_end  # Update current time after meeting

# Output the schedule as a JSON-formatted dictionary
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))