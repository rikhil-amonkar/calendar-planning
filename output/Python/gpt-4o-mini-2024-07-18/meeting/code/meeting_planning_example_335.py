import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Mission District"): 15,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Mission District"): 18,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Mission District"): 17,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Financial District"): 17,
    ("Mission District", "Alamo Square"): 11
}

# Meeting constraints and available times
meetings = {
    "Helen": {"location": "North Beach", "start": "09:00", "end": "17:00", "duration": 15},
    "Betty": {"location": "Financial District", "start": "19:00", "end": "21:45", "duration": 90},
    "Amanda": {"location": "Alamo Square", "start": "19:45", "end": "21:00", "duration": 60},
    "Kevin": {"location": "Mission District", "start": "10:45", "end": "14:45", "duration": 45},
}

# Function to convert time string to datetime object
def time_str_to_dt(time_str):
    return datetime.strptime(time_str, "%H:%M")

# Function to convert datetime object to time string
def dt_to_time_str(dt):
    return dt.strftime("%H:%M")

# Start at Pacific Heights at 09:00
current_time = time_str_to_dt("09:00")
itinerary = []

# Meeting Helen
helen_meeting_start = current_time
helen_meeting_end = helen_meeting_start + timedelta(minutes=meetings["Helen"]["duration"])

if helen_meeting_end <= time_str_to_dt(meetings["Helen"]["end"]):
    itinerary.append({
        "action": "meet",
        "location": meetings["Helen"]["location"],
        "person": "Helen",
        "start_time": dt_to_time_str(helen_meeting_start),
        "end_time": dt_to_time_str(helen_meeting_end)
    })
    current_time = helen_meeting_end + timedelta(minutes=travel_times[("North Beach", "Mission District")])

# Meeting Kevin
kevin_meeting_start = max(current_time, time_str_to_dt(meetings["Kevin"]["start"]))
kevin_meeting_end = kevin_meeting_start + timedelta(minutes=meetings["Kevin"]["duration"])

if kevin_meeting_end <= time_str_to_dt(meetings["Kevin"]["end"]):
    itinerary.append({
        "action": "meet",
        "location": meetings["Kevin"]["location"],
        "person": "Kevin",
        "start_time": dt_to_time_str(kevin_meeting_start),
        "end_time": dt_to_time_str(kevin_meeting_end)
    })
    current_time = kevin_meeting_end + timedelta(minutes=travel_times[("Mission District", "Alamo Square")])

# Meeting Amanda
amanda_meeting_start = max(current_time, time_str_to_dt(meetings["Amanda"]["start"]))
amanda_meeting_end = amanda_meeting_start + timedelta(minutes=meetings["Amanda"]["duration"])

if amanda_meeting_end <= time_str_to_dt(meetings["Amanda"]["end"]):
    itinerary.append({
        "action": "meet",
        "location": meetings["Amanda"]["location"],
        "person": "Amanda",
        "start_time": dt_to_time_str(amanda_meeting_start),
        "end_time": dt_to_time_str(amanda_meeting_end)
    })
    current_time = amanda_meeting_end + timedelta(minutes=travel_times[("Alamo Square", "Financial District")])

# Meeting Betty
betty_meeting_start = max(current_time, time_str_to_dt(meetings["Betty"]["start"]))
betty_meeting_end = betty_meeting_start + timedelta(minutes=meetings["Betty"]["duration"])

if betty_meeting_end <= time_str_to_dt(meetings["Betty"]["end"]):
    itinerary.append({
        "action": "meet",
        "location": meetings["Betty"]["location"],
        "person": "Betty",
        "start_time": dt_to_time_str(betty_meeting_start),
        "end_time": dt_to_time_str(betty_meeting_end)
    })

# Outputting the itinerary as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))