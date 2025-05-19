import json
from datetime import datetime, timedelta

# Constants for travel times
travel_times = {
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Fisherman\'s Wharf', 'The Castro'): 26,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Russian Hill'): 7,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Russian Hill'): 13,
    ('North Beach', 'Russian Hill'): 5,
}

# Meeting constraints
participants = {
    "Carol": {"location": "Haight-Ashbury", "available": (datetime.strptime("21:30", "%H:%M"), datetime.strptime("22:30", "%H:%M")), "duration": 60},
    "Laura": {"location": "Fisherman\'s Wharf", "available": (datetime.strptime("11:45", "%H:%M"), datetime.strptime("21:30", "%H:%M")), "duration": 60},
    "Karen": {"location": "The Castro", "available": (datetime.strptime("07:15", "%H:%M"), datetime.strptime("14:00", "%H:%M")), "duration": 75},
    "Elizabeth": {"location": "Chinatown", "available": (datetime.strptime("12:15", "%H:%M"), datetime.strptime("21:30", "%H:%M")), "duration": 75},
    "Deborah": {"location": "Alamo Square", "available": (datetime.strptime("12:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")), "duration": 105},
    "Jason": {"location": "North Beach", "available": (datetime.strptime("14:45", "%H:%M"), datetime.strptime("19:00", "%H:%M")), "duration": 90},
    "Steven": {"location": "Russian Hill", "available": (datetime.strptime("14:45", "%H:%M"), datetime.strptime("18:30", "%H:%M")), "duration": 120},
}

# Start time
start_time = datetime.strptime("09:00", "%H:%M")
itinerary = []

# Function to add a meeting to the itinerary
def add_meeting(location, person, start, duration):
    end = start + timedelta(minutes=duration)
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": start.strftime("%H:%M"),
        "end_time": end.strftime("%H:%M")
    })
    return end

# Meeting logic
current_time = start_time

# Meeting Karen
if current_time < participants["Karen"]["available"][1]:
    travel_time = travel_times[('Golden Gate Park', 'The Castro')]
    current_time += timedelta(minutes=travel_time)
    if current_time < participants["Karen"]["available"][0]:
        current_time = participants["Karen"]["available"][0]
    current_time = add_meeting("The Castro", "Karen", current_time, participants["Karen"]["duration"])

# Meeting Deborah
if current_time < participants["Deborah"]["available"][1]:
    travel_time = travel_times[('The Castro', 'Alamo Square')]
    current_time += timedelta(minutes=travel_time)
    if current_time < participants["Deborah"]["available"][0]:
        current_time = participants["Deborah"]["available"][0]
    current_time = add_meeting("Alamo Square", "Deborah", current_time, participants["Deborah"]["duration"])

# Meeting Jason
if current_time < participants["Jason"]["available"][1]:
    travel_time = travel_times[('Alamo Square', 'North Beach')]
    current_time += timedelta(minutes=travel_time)
    if current_time < participants["Jason"]["available"][0]:
        current_time = participants["Jason"]["available"][0]
    current_time = add_meeting("North Beach", "Jason", current_time, participants["Jason"]["duration"])

# Meeting Steven
if current_time < participants["Steven"]["available"][1]:
    travel_time = travel_times[('North Beach', 'Russian Hill')]
    current_time += timedelta(minutes=travel_time)
    if current_time < participants["Steven"]["available"][0]:
        current_time = participants["Steven"]["available"][0]
    current_time = add_meeting("Russian Hill", "Steven", current_time, participants["Steven"]["duration"])

# Meeting Elizabeth
if current_time < participants["Elizabeth"]["available"][1]:
    travel_time = travel_times[('Russian Hill', 'Chinatown')]
    current_time += timedelta(minutes=travel_time)
    if current_time < participants["Elizabeth"]["available"][0]:
        current_time = participants["Elizabeth"]["available"][0]
    current_time = add_meeting("Chinatown", "Elizabeth", current_time, participants["Elizabeth"]["duration"])

# Meeting Laura
if current_time < participants["Laura"]["available"][1]:
    travel_time = travel_times[('Chinatown', 'Fisherman\'s Wharf')]
    current_time += timedelta(minutes=travel_time)
    if current_time < participants["Laura"]["available"][0]:
        current_time = participants["Laura"]["available"][0]
    current_time = add_meeting("Fisherman\'s Wharf", "Laura", current_time, participants["Laura"]["duration"])

# Meeting Carol
if current_time < participants["Carol"]["available"][1]:
    travel_time = travel_times[('Fisherman\'s Wharf', 'Haight-Ashbury')]
    current_time += timedelta(minutes=travel_time)
    if current_time < participants["Carol"]["available"][0]:
        current_time = participants["Carol"]["available"][0]
    current_time = add_meeting("Haight-Ashbury", "Carol", current_time, participants["Carol"]["duration"])

# Output the result in JSON format
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))