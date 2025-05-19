import json
from datetime import datetime, timedelta

# Define the travel distances (in minutes)
travel_times = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Financial District"): 30,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Financial District"): 17,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Financial District"): 11,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Financial District"): 23,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Presidio"): 22,
}

# Define meeting constraints
meetings = {
    "Kevin": {
        "location": "Alamo Square",
        "start": "09:00",
        "end": "21:30",
        "min_duration": 75
    },
    "Kimberly": {
        "location": "Russian Hill",
        "start": "08:45",
        "end": "12:30",
        "min_duration": 30
    },
    "Joseph": {
        "location": "Presidio",
        "start": "18:30",
        "end": "19:15",
        "min_duration": 45
    },
    "Thomas": {
        "location": "Financial District",
        "start": "19:00",
        "end": "21:45",
        "min_duration": 45
    },
}

# Convert time strings to datetime
def str_to_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

# Convert datetime to required time format
def time_to_str(dt):
    return dt.strftime("%H:%M")

# Calculate meeting schedules
def schedule_meetings():
    start_time = str_to_time("09:00")
    itinerary = []
    
    # Meeting Kevin
    kevin_start = start_time + timedelta(minutes=travel_times[("Sunset District", "Alamo Square")])
    kevin_end = kevin_start + timedelta(minutes=meetings["Kevin"]["min_duration"])

    if kevin_end.time() <= str_to_time(meetings["Kevin"]["end"]).time():
        itinerary.append({
            "action": "meet",
            "location": "Alamo Square",
            "person": "Kevin",
            "start_time": time_to_str(kevin_start),
            "end_time": time_to_str(kevin_end),
        })

    # Meeting Kimberly
    sunset_to_russian_hill = travel_times[("Sunset District", "Russian Hill")]
    kimberly_start = max(str_to_time(meetings["Kimberly"]["start"]),
                          kevin_end + timedelta(minutes=travel_times[("Alamo Square", "Russian Hill")]))
    kimberly_end = kimberly_start + timedelta(minutes=meetings["Kimberly"]["min_duration"])

    if kimberly_end.time() <= str_to_time(meetings["Kimberly"]["end"]).time():
        itinerary.append({
            "action": "meet",
            "location": "Russian Hill",
            "person": "Kimberly",
            "start_time": time_to_str(kimberly_start),
            "end_time": time_to_str(kimberly_end),
        })

    # Meeting Joseph
    time_after_russian_hill = kimberly_end + timedelta(minutes=travel_times[("Russian Hill", "Presidio")])
    joseph_start = max(time_after_russian_hill, str_to_time(meetings["Joseph"]["start"]))
    joseph_end = joseph_start + timedelta(minutes=meetings["Joseph"]["min_duration"])

    if joseph_end.time() <= str_to_time(meetings["Joseph"]["end"]).time():
        itinerary.append({
            "action": "meet",
            "location": "Presidio",
            "person": "Joseph",
            "start_time": time_to_str(joseph_start),
            "end_time": time_to_str(joseph_end),
        })

    # Meeting Thomas
    time_after_joseph = joseph_end + timedelta(minutes=travel_times[("Presidio", "Financial District")])
    thomas_start = max(time_after_joseph, str_to_time(meetings["Thomas"]["start"]))
    thomas_end = thomas_start + timedelta(minutes=meetings["Thomas"]["min_duration"])

    if thomas_end.time() <= str_to_time(meetings["Thomas"]["end"]).time():
        itinerary.append({
            "action": "meet",
            "location": "Financial District",
            "person": "Thomas",
            "start_time": time_to_str(thomas_start),
            "end_time": time_to_str(thomas_end),
        })

    return {"itinerary": itinerary}

# Execute the scheduling
optimal_schedule = schedule_meetings()

# Output the result as JSON
print(json.dumps(optimal_schedule, indent=2))