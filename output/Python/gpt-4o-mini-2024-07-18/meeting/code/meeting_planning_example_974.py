import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    ("Sunset District", "Presidio"): 16,
    ("Presidio", "Nob Hill"): 18,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Pacific Heights", "Mission District"): 15,
    ("Mission District", "Marina District"): 20,
    ("Marina District", "North Beach"): 11,
    ("North Beach", "Russian Hill"): 5,
    ("Russian Hill", "Richmond District"): 14,
    ("Richmond District", "Embarcadero"): 19,
    ("Embarcadero", "Alamo Square"): 19,
    # Additional necessary routes
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Alamo Square"): 17,
    # and so on for combinations...
}

# Participant constraints
participants = {
    "Charles": {"location": "Presidio", "start": "13:15", "end": "15:00", "min_time": 105},
    "Robert": {"location": "Nob Hill", "start": "13:15", "end": "17:30", "min_time": 90},
    "Nancy": {"location": "Pacific Heights", "start": "14:45", "end": "22:00", "min_time": 105},
    "Brian": {"location": "Mission District", "start": "15:30", "end": "22:00", "min_time": 60},
    "Kimberly": {"location": "Marina District", "start": "17:00", "end": "19:45", "min_time": 75},
    "David": {"location": "North Beach", "start": "14:45", "end": "16:30", "min_time": 75},
    "William": {"location": "Russian Hill", "start": "12:30", "end": "19:15", "min_time": 120},
    "Jeffrey": {"location": "Richmond District", "start": "12:00", "end": "19:15", "min_time": 45},
    "Karen": {"location": "Embarcadero", "start": "14:15", "end": "20:45", "min_time": 60},
    "Joshua": {"location": "Alamo Square", "start": "18:45", "end": "22:00", "min_time": 60},
}

# Meeting scheduling logic
start_meeting_time = datetime.strptime("09:00", "%H:%M")
itinerary = []

def add_meeting(person, start, duration):
    end_time = start + timedelta(minutes=duration)
    itinerary.append({"action": "meet", "location": participants[person]["location"],
                      "person": person, "start_time": start.strftime("%H:%M"),
                      "end_time": end_time.strftime("%H:%M")})
    return end_time

# Function to find the next meeting slot
def find_meeting_schedule(current_time):
    for person, details in participants.items():
        available_start = datetime.strptime(details["start"], "%H:%M")
        available_end = datetime.strptime(details["end"], "%H:%M")
        duration = details["min_time"]
        travel_time = travel_times.get((current_location, details["location"]), float('inf'))

        if current_time + timedelta(minutes=travel_time) <= available_start:
            # Travel in the morning before meeting
            arrival_time = available_start
        else:
            arrival_time = current_time + timedelta(minutes=travel_time)

        if arrival_time + timedelta(minutes=duration) <= available_end:
            # We can schedule a meeting
            current_time = add_meeting(person, arrival_time, duration)
            current_location = details["location"]

# Start scheduling
current_location = "Sunset District"
current_time = start_meeting_time

# Execute scheduling
find_meeting_schedule(current_time)

# Output the itinerary in JSON format
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))