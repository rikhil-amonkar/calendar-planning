import json
from datetime import datetime, timedelta
from itertools import permutations

# Input parameters
locations = {
    "Alamo Square": {"name": "Alamo Square"},
    "Russian Hill": {"name": "Russian Hill"},
    "Presidio": {"name": "Presidio"},
    "Chinatown": {"name": "Chinatown"},
    "Sunset District": {"name": "Sunset District"},
    "The Castro": {"name": "The Castro"},
    "Embarcadero": {"name": "Embarcadero"},
    "Golden Gate Park": {"name": "Golden Gate Park"}
}

travel_times = {
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Embarcadero"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Embarcadero"): 31,
    ("Sunset District", "Golden Gate Park"): 11,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Chinatown"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "The Castro"): 13,
}

constraints = {
    "Emily": {"location": "Russian Hill", "start": "12:15", "end": "14:15", "duration": 105},
    "Mark": {"location": "Presidio", "start": "14:45", "end": "19:30", "duration": 60},
    "Deborah": {"location": "Chinatown", "start": "7:30", "end": "15:30", "duration": 45},
    "Margaret": {"location": "Sunset District", "start": "21:30", "end": "22:30", "duration": 60},
    "George": {"location": "The Castro", "start": "7:30", "end": "14:15", "duration": 60},
    "Andrew": {"location": "Embarcadero", "start": "20:15", "end": "22:00", "duration": 75},
    "Steven": {"location": "Golden Gate Park", "start": "11:15", "end": "21:15", "duration": 105},
}

arrival_time = datetime.strptime("09:00", "%H:%M")
itinerary = []

# Helper function to check if time overlaps
def overlaps(start1, end1, start2, end2):
    return not (end1 <= start2 or end2 <= start1)

# Helper function to try scheduling meetings
def schedule_meeting(person, start_time):
    location = constraints[person]['location']
    meet_duration = constraints[person]['duration']
    
    start_time_dt = datetime.combine(start_time.date(), start_time.time())
    end_time_dt = start_time_dt + timedelta(minutes=meet_duration)

    if start_time_dt.time() >= datetime.strptime(constraints[person]['start'], "%H:%M").time() and \
       end_time_dt.time() <= datetime.strptime(constraints[person]['end'], "%H:%M").time():
        return start_time_dt, end_time_dt, location
    return None

# Main scheduling routine
def schedule_visits(current_time, visited):
    for person in constraints.keys():
        if person not in visited:
            meeting = schedule_meeting(person, current_time)
            if meeting:
                start_time, end_time, location = meeting 
                travel_time = travel_times.get((locations[location]["name"], locations["Alamo Square"]["name"]), 0)
                travel_back_time = travel_times.get((locations["Alamo Square"]["name"], locations[location]["name"]), 0)
                
                # Adding to itinerary
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": start_time.strftime("%H:%M"),
                    "end_time": end_time.strftime("%H:%M")
                })
                
                # Move current time to after meeting plus return to previous location
                current_time = end_time + timedelta(minutes=travel_back_time)
                visited.add(person)

                # Schedule next visits
                schedule_visits(current_time, visited)

# Start scheduling from Alamo Square
schedule_visits(arrival_time, set())

# Preparing output
result = {
    "itinerary": itinerary,
}

# Print the result as JSON
print(json.dumps(result, indent=2))