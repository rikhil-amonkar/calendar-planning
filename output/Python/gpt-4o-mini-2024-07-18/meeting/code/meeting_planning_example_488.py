import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Sunset District"): 25,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Sunset District"): 15,
}

# Meeting constraints
constraints = {
    "Ronald": {"location": "Nob Hill", "available_from": "10:00", "available_to": "17:00", "min_time": 105},
    "Sarah": {"location": "Russian Hill", "available_from": "07:15", "available_to": "09:30", "min_time": 45},
    "Helen": {"location": "The Castro", "available_from": "13:30", "available_to": "17:00", "min_time": 120},
    "Joshua": {"location": "Sunset District", "available_from": "14:15", "available_to": "19:30", "min_time": 90},
    "Margaret": {"location": "Haight-Ashbury", "available_from": "10:15", "available_to": "22:00", "min_time": 60},
}

# Starting time
start_time = datetime.strptime("09:00", "%H:%M")
current_time = start_time

itinerary = []

# Meeting Sarah first since she is available before everyone else
if current_time < datetime.strptime(constraints["Sarah"]["available_to"], "%H:%M"):
    meet_time = current_time + timedelta(minutes=travel_times[("Pacific Heights", "Russian Hill")])
    if meet_time + timedelta(minutes=constraints["Sarah"]["min_time"]) <= datetime.strptime(constraints["Sarah"]["available_to"], "%H:%M"):
        itinerary.append({
            "action": "meet",
            "location": "Russian Hill",
            "person": "Sarah",
            "start_time": meet_time.strftime("%H:%M"),
            "end_time": (meet_time + timedelta(minutes=constraints["Sarah"]["min_time"])).strftime("%H:%M"),
        })
        current_time = meet_time + timedelta(minutes=constraints["Sarah"]["min_time"] + travel_times[("Russian Hill", "Nob Hill")])

# Meeting Ronald next 
if current_time < datetime.strptime(constraints["Ronald"]["available_to"], "%H:%M"):
    meet_time = current_time + timedelta(minutes=travel_times[("Nob Hill", "Pacific Heights")])
    if meet_time + timedelta(minutes=constraints["Ronald"]["min_time"]) <= datetime.strptime(constraints["Ronald"]["available_to"], "%H:%M"):
        itinerary.append({
            "action": "meet",
            "location": "Nob Hill",
            "person": "Ronald",
            "start_time": meet_time.strftime("%H:%M"),
            "end_time": (meet_time + timedelta(minutes=constraints["Ronald"]["min_time"])).strftime("%H:%M"),
        })
        current_time = meet_time + timedelta(minutes=constraints["Ronald"]["min_time"] + travel_times[("Nob Hill", "The Castro")])

# Meeting Helen next
if current_time < datetime.strptime(constraints["Helen"]["available_to"], "%H:%M"):
    meet_time = current_time + timedelta(minutes=travel_times[("The Castro", "Nob Hill")])
    if meet_time + timedelta(minutes=constraints["Helen"]["min_time"]) <= datetime.strptime(constraints["Helen"]["available_to"], "%H:%M"):
        itinerary.append({
            "action": "meet",
            "location": "The Castro",
            "person": "Helen",
            "start_time": meet_time.strftime("%H:%M"),
            "end_time": (meet_time + timedelta(minutes=constraints["Helen"]["min_time"])).strftime("%H:%M"),
        })
        current_time = meet_time + timedelta(minutes=constraints["Helen"]["min_time"] + travel_times[("The Castro", "Sunset District")])

# Meeting Joshua finally
if current_time < datetime.strptime(constraints["Joshua"]["available_to"], "%H:%M"):
    meet_time = current_time + timedelta(minutes=travel_times[("Sunset District", "The Castro")])
    if meet_time + timedelta(minutes=constraints["Joshua"]["min_time"]) <= datetime.strptime(constraints["Joshua"]["available_to"], "%H:%M"):
        itinerary.append({
            "action": "meet",
            "location": "Sunset District",
            "person": "Joshua",
            "start_time": meet_time.strftime("%H:%M"),
            "end_time": (meet_time + timedelta(minutes=constraints["Joshua"]["min_time"])).strftime("%H:%M"),
        })

# Meeting Margaret last
if current_time < datetime.strptime(constraints["Margaret"]["available_to"], "%H:%M"):
    meet_time = current_time + timedelta(minutes=travel_times[("Haight-Ashbury", "Sunset District")])
    if meet_time + timedelta(minutes=constraints["Margaret"]["min_time"]) <= datetime.strptime(constraints["Margaret"]["available_to"], "%H:%M"):
        itinerary.append({
            "action": "meet",
            "location": "Haight-Ashbury",
            "person": "Margaret",
            "start_time": meet_time.strftime("%H:%M"),
            "end_time": (meet_time + timedelta(minutes=constraints["Margaret"]["min_time"])).strftime("%H:%M"),
        })

# Output in JSON format
output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))