import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Mission District"): 24,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Mission District"): 10,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Mission District"): 16,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Mission District"): 17,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Golden Gate Park"): 17,
}

# Define meeting constraints
meetings = {
    "Charles": {"location": "Alamo Square", "start": "18:00", "end": "20:45", "min_duration": 90},
    "Margaret": {"location": "Russian Hill", "start": "9:00", "end": "16:00", "min_duration": 30},
    "Daniel": {"location": "Golden Gate Park", "start": "8:00", "end": "13:30", "min_duration": 15},
    "Stephanie": {"location": "Mission District", "start": "20:30", "end": "22:00", "min_duration": 90},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_to_str(time_obj):
    return time_obj.strftime("%H:%M")

def can_meet(start, end, min_duration):
    duration = (parse_time(end) - parse_time(start)).total_seconds() / 60
    return duration >= min_duration

def find_schedule():
    current_location = "Sunset District"
    current_time = parse_time("9:00")
    itinerary = []

    def add_meeting(person, location, start, end):
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": start,
            "end_time": end
        })

    # Try to meet Margaret first since she's available early
    if can_meet(meetings["Margaret"]["start"], meetings["Margaret"]["end"], meetings["Margaret"]["min_duration"]):
        travel_time = travel_times[(current_location, meetings["Margaret"]["location"])]
        arrival_time = current_time + timedelta(minutes=travel_time)
        if arrival_time <= parse_time(meetings["Margaret"]["end"]) - timedelta(minutes=meetings["Margaret"]["min_duration"]):
            add_meeting("Margaret", meetings["Margaret"]["location"], time_to_str(arrival_time), time_to_str(arrival_time + timedelta(minutes=meetings["Margaret"]["min_duration"])))
            current_location = meetings["Margaret"]["location"]
            current_time = arrival_time + timedelta(minutes=meetings["Margaret"]["min_duration"])

    # Try to meet Daniel next
    if can_meet(meetings["Daniel"]["start"], meetings["Daniel"]["end"], meetings["Daniel"]["min_duration"]):
        travel_time = travel_times[(current_location, meetings["Daniel"]["location"])]
        arrival_time = current_time + timedelta(minutes=travel_time)
        if arrival_time <= parse_time(meetings["Daniel"]["end"]) - timedelta(minutes=meetings["Daniel"]["min_duration"]):
            add_meeting("Daniel", meetings["Daniel"]["location"], time_to_str(arrival_time), time_to_str(arrival_time + timedelta(minutes=meetings["Daniel"]["min_duration"])))
            current_location = meetings["Daniel"]["location"]
            current_time = arrival_time + timedelta(minutes=meetings["Daniel"]["min_duration"])

    # Try to meet Charles last since he's available late
    charles_start = parse_time(meetings["Charles"]["start"])
    charles_end = parse_time(meetings["Charles"]["end"])
    travel_time = travel_times[(current_location, meetings["Charles"]["location"])]
    potential_arrival_time = current_time + timedelta(minutes=travel_time)
    
    # Adjust the start time for Charles if necessary
    if potential_arrival_time < charles_start:
        potential_arrival_time = charles_start
    
    if can_meet(time_to_str(potential_arrival_time), meetings["Charles"]["end"], meetings["Charles"]["min_duration"]):
        add_meeting("Charles", meetings["Charles"]["location"], time_to_str(potential_arrival_time), time_to_str(potential_arrival_time + timedelta(minutes=meetings["Charles"]["min_duration"])))
        current_location = meetings["Charles"]["location"]
        current_time = potential_arrival_time + timedelta(minutes=meetings["Charles"]["min_duration"])

    # Try to meet Stephanie if there's time
    if can_meet(meetings["Stephanie"]["start"], meetings["Stephanie"]["end"], meetings["Stephanie"]["min_duration"]):
        travel_time = travel_times[(current_location, meetings["Stephanie"]["location"])]
        arrival_time = current_time + timedelta(minutes=travel_time)
        if arrival_time <= parse_time(meetings["Stephanie"]["end"]) - timedelta(minutes=meetings["Stephanie"]["min_duration"]):
            add_meeting("Stephanie", meetings["Stephanie"]["location"], time_to_str(arrival_time), time_to_str(arrival_time + timedelta(minutes=meetings["Stephanie"]["min_duration"])))

    return itinerary

schedule = find_schedule()
print(json.dumps({"itinerary": schedule}, indent=2))