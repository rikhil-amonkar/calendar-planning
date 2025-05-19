import json
from datetime import datetime, timedelta

# Travel times (in minutes)
travel_times = {
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Marina District"): 25,
    ("Bayview", "Embarcadero"): 19,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Nob Hill", "Marina District"): 12,
    ("Nob Hill", "Embarcadero"): 9,
    ("Marina District", "Embarcadero"): 12,
}

# Meeting Constraints
constraints = {
    "Thomas": {"location": "Bayview", "start": "15:30", "end": "18:30", "min_duration": 120},
    "Stephanie": {"location": "Golden Gate Park", "start": "18:30", "end": "21:45", "min_duration": 30},
    "Laura": {"location": "Nob Hill", "start": "08:45", "end": "16:15", "min_duration": 30},
    "Betty": {"location": "Marina District", "start": "18:45", "end": "21:45", "min_duration": 45},
    "Patricia": {"location": "Embarcadero", "start": "17:30", "end": "22:00", "min_duration": 45},
}

# Helper functions
def time_to_datetime(time_str):
    return datetime.strptime(time_str, "%H:%M")

def add_minutes(start_time, minutes):
    return start_time + timedelta(minutes=minutes)

def format_time(dt):
    return dt.strftime("%H:%M")

# Itinerary calculation
itinerary = []
current_time = time_to_datetime("09:00")

# Meet Laura
laura_start = time_to_datetime(constraints["Laura"]["start"])
laura_end = time_to_datetime(constraints["Laura"]["end"])

if current_time < laura_start:
    travel_time = travel_times[("Fisherman's Wharf", "Nob Hill")]
    current_time = add_minutes(current_time, travel_time)
    
if current_time < laura_end:
    meet_duration = 30
    end_time = add_minutes(current_time, meet_duration)
    if end_time > laura_end:
        end_time = laura_end
        meet_duration = (end_time - current_time).seconds // 60
        
    itinerary.append({
        "action": "meet",
        "location": constraints["Laura"]["location"],
        "person": "Laura",
        "start_time": format_time(current_time),
        "end_time": format_time(end_time)
    })
    current_time = end_time

# Meet Thomas
thomas_start = time_to_datetime(constraints["Thomas"]["start"])
thomas_end = time_to_datetime(constraints["Thomas"]["end"])

if current_time < thomas_start:
    travel_time = travel_times[("Nob Hill", "Bayview")]
    current_time = add_minutes(current_time, travel_time)

if current_time < thomas_end:
    meet_duration = 120
    end_time = add_minutes(current_time, meet_duration)
    if end_time > thomas_end:
        end_time = thomas_end
        meet_duration = (end_time - current_time).seconds // 60
    
    itinerary.append({
        "action": "meet",
        "location": constraints["Thomas"]["location"],
        "person": "Thomas",
        "start_time": format_time(current_time),
        "end_time": format_time(end_time)
    })
    current_time = end_time

# Meet Patricia
patricia_start = time_to_datetime(constraints["Patricia"]["start"])
patricia_end = time_to_datetime(constraints["Patricia"]["end"])

if current_time < patricia_start:
    travel_time = travel_times[("Bayview", "Embarcadero")]
    current_time = add_minutes(current_time, travel_time)

if current_time < patricia_end:
    meet_duration = 45
    end_time = add_minutes(current_time, meet_duration)
    if end_time > patricia_end:
        end_time = patricia_end
        meet_duration = (end_time - current_time).seconds // 60
    
    itinerary.append({
        "action": "meet",
        "location": constraints["Patricia"]["location"],
        "person": "Patricia",
        "start_time": format_time(current_time),
        "end_time": format_time(end_time)
    })
    current_time = end_time

# Meet Betty
betty_start = time_to_datetime(constraints["Betty"]["start"])
betty_end = time_to_datetime(constraints["Betty"]["end"])

if current_time < betty_start:
    travel_time = travel_times[("Embarcadero", "Marina District")]
    current_time = add_minutes(current_time, travel_time)

if current_time < betty_end:
    meet_duration = 45
    end_time = add_minutes(current_time, meet_duration)
    if end_time > betty_end:
        end_time = betty_end
        meet_duration = (end_time - current_time).seconds // 60
    
    itinerary.append({
        "action": "meet",
        "location": constraints["Betty"]["location"],
        "person": "Betty",
        "start_time": format_time(current_time),
        "end_time": format_time(end_time)
    })
    current_time = end_time

# Meet Stephanie
stephanie_start = time_to_datetime(constraints["Stephanie"]["start"])
stephanie_end = time_to_datetime(constraints["Stephanie"]["end"])

if current_time < stephanie_start:
    travel_time = travel_times[("Marina District", "Golden Gate Park")]
    current_time = add_minutes(current_time, travel_time)

if current_time < stephanie_end:
    meet_duration = 30
    end_time = add_minutes(current_time, meet_duration)
    if end_time > stephanie_end:
        end_time = stephanie_end
        meet_duration = (end_time - current_time).seconds // 60
    
    itinerary.append({
        "action": "meet",
        "location": constraints["Stephanie"]["location"],
        "person": "Stephanie",
        "start_time": format_time(current_time),
        "end_time": format_time(end_time)
    })

# Output itinerary as JSON
output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))