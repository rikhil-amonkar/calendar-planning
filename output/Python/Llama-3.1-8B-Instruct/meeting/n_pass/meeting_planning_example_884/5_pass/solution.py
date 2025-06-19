import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_distances = {
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 27,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 20,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Bayview"): 22,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Bayview"): 16,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Bayview"): 19,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Bayview"): 25,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Bayview"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Bayview"): 23,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Golden Gate Park"): 22
}

# Meeting constraints
constraints = {
    "Robert": {"start_time": "07:45", "end_time": "17:30", "duration": 120},
    "David": {"start_time": "12:30", "end_time": "19:45", "duration": 45},
    "Matthew": {"start_time": "08:45", "end_time": "13:45", "duration": 90},
    "Jessica": {"start_time": "09:30", "end_time": "18:45", "duration": 45},
    "Melissa": {"start_time": "07:15", "end_time": "16:45", "duration": 45},
    "Mark": {"start_time": "15:15", "end_time": "17:00", "duration": 45},
    "Deborah": {"start_time": "19:00", "end_time": "19:45", "duration": 45},
    "Karen": {"start_time": "19:30", "end_time": "22:00", "duration": 120},
    "Laura": {"start_time": "21:15", "end_time": "22:15", "duration": 15}
}

# Current location
current_location = "Richmond District"
current_time = datetime.strptime("09:00", "%H:%M")

# Itinerary
itinerary = []

# Function to calculate travel time
def calculate_travel_time(location):
    return travel_distances[(current_location, location)] / 60

# Function to add meeting to itinerary
def add_meeting(person, location):
    global current_time, itinerary
    start_time = datetime.strptime(constraint["start_time"], "%H:%M")
    end_time = datetime.strptime(constraint["end_time"], "%H:%M")
    travel_time = calculate_travel_time(location)
    start_time += timedelta(minutes=travel_time)
    end_time += timedelta(minutes=travel_time)
    if start_time < current_time:
        print(f"Cannot schedule meeting for {person} at {location} due to early start time.")
        return
    if end_time < current_time:
        print(f"Cannot schedule meeting for {person} at {location} due to end time before current time.")
        return
    available_time = end_time - start_time
    available_time -= timedelta(minutes=constraints[person]["duration"])
    if available_time < timedelta(minutes=0):
        print(f"Cannot schedule meeting for {person} at {location} due to conflicting constraints.")
        return
    if any(m["location"] == location for m in itinerary):
        print(f"Cannot schedule meeting for {person} at {location} due to existing meeting.")
        return
    itinerary.append({"action": "meet", "location": location, "person": person, "start_time": start_time.strftime("%H:%M"), "end_time": end_time.strftime("%H:%M")})
    current_time = end_time

# Main loop
for person, constraint in constraints.items():
    if person == "Robert":
        start_time = datetime.strptime(constraint["start_time"], "%H:%M")
        if current_time < start_time:
            add_meeting(person, "Chinatown")
            current_time += timedelta(minutes=constraints[person]["duration"])
        else:
            current_time = start_time
            add_meeting(person, "Chinatown")
    elif person == "David":
        start_time = datetime.strptime(constraint["start_time"], "%H:%M")
        if current_time < start_time:
            add_meeting(person, "Sunset District")
            current_time += timedelta(minutes=constraints[person]["duration"])
        else:
            current_time = start_time
            add_meeting(person, "Sunset District")
    elif person == "Matthew":
        start_time = datetime.strptime(constraint["start_time"], "%H:%M")
        if current_time < start_time:
            add_meeting(person, "Alamo Square")
            current_time += timedelta(minutes=constraints[person]["duration"])
        else:
            current_time = start_time
            add_meeting(person, "Alamo Square")
    elif person == "Jessica":
        start_time = datetime.strptime(constraint["start_time"], "%H:%M")
        if current_time < start_time:
            add_meeting(person, "Financial District")
            current_time += timedelta(minutes=constraints[person]["duration"])
        else:
            current_time = start_time
            add_meeting(person, "Financial District")
    elif person == "Melissa":
        start_time = datetime.strptime(constraint["start_time"], "%H:%M")
        if current_time < start_time:
            add_meeting(person, "North Beach")
            current_time += timedelta(minutes=constraints[person]["duration"])
        else:
            current_time = start_time
            add_meeting(person, "North Beach")
    elif person == "Mark":
        start_time = datetime.strptime(constraint["start_time"], "%H:%M")
        if current_time < start_time:
            add_meeting(person, "Embarcadero")
            current_time += timedelta(minutes=constraints[person]["duration"])
        else:
            current_time = start_time
            add_meeting(person, "Embarcadero")
    elif person == "Deborah":
        start_time = datetime.strptime(constraint["start_time"], "%H:%M")
        if current_time < start_time:
            add_meeting(person, "Presidio")
            current_time += timedelta(minutes=constraints[person]["duration"])
        else:
            current_time = start_time
            add_meeting(person, "Presidio")
    elif person == "Karen":
        start_time = datetime.strptime(constraint["start_time"], "%H:%M")
        if current_time < start_time:
            add_meeting(person, "Golden Gate Park")
            current_time += timedelta(minutes=constraints[person]["duration"])
        else:
            current_time = start_time
            add_meeting(person, "Golden Gate Park")
    elif person == "Laura":
        start_time = datetime.strptime(constraint["start_time"], "%H:%M")
        if current_time < start_time:
            add_meeting(person, "Bayview")
            current_time += timedelta(minutes=constraints[person]["duration"])
        else:
            current_time = start_time
            add_meeting(person, "Bayview")

# Output itinerary as JSON
print(json.dumps({"itinerary": itinerary}, indent=4))