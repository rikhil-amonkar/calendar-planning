import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Financial District"): 22,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Richmond District"): 21,
}

# Define constraints
arrival_time = datetime.strptime('09:00', '%H:%M')
meetings = {
    "Emily": {
        "location": "Presidio",
        "available_start": datetime.strptime('16:15', '%H:%M'),
        "available_end": datetime.strptime('21:00', '%H:%M'),
        "min_duration": 105,  # in minutes
    },
    "Joseph": {
        "location": "Richmond District",
        "available_start": datetime.strptime('17:15', '%H:%M'),
        "available_end": datetime.strptime('22:00', '%H:%M'),
        "min_duration": 120,  # in minutes
    },
    "Melissa": {
        "location": "Financial District",
        "available_start": datetime.strptime('15:45', '%H:%M'),
        "available_end": datetime.strptime('21:45', '%H:%M'),
        "min_duration": 75,  # in minutes
    },
}

# Generate meeting schedule
itinerary = []
current_time = arrival_time

# Meet Melissa first as she is available before others
if current_time < meetings["Melissa"]["available_end"]:
    travel_time = travel_times[("Fisherman's Wharf", "Financial District")]
    start_time_melissa = max(current_time + timedelta(minutes=travel_time), meetings["Melissa"]["available_start"])
    end_time_melissa = start_time_melissa + timedelta(minutes=meetings["Melissa"]["min_duration"])
    
    # Check if meeting with Melissa ends before she is unavailable
    if end_time_melissa <= meetings["Melissa"]["available_end"]:
        itinerary.append({
            "action": "meet",
            "location": "Financial District",
            "person": "Melissa",
            "start_time": start_time_melissa.strftime('%H:%M'),
            "end_time": end_time_melissa.strftime('%H:%M'),
        })
        current_time = end_time_melissa

# Now meet Joseph
if current_time < meetings["Joseph"]["available_end"]:
    travel_time = travel_times[("Financial District", "Richmond District")]
    start_time_joseph = max(current_time + timedelta(minutes=travel_time), meetings["Joseph"]["available_start"])
    end_time_joseph = start_time_joseph + timedelta(minutes=meetings["Joseph"]["min_duration"])
    
    # Check if meeting with Joseph ends before he is unavailable
    if end_time_joseph <= meetings["Joseph"]["available_end"]:
        itinerary.append({
            "action": "meet",
            "location": "Richmond District",
            "person": "Joseph",
            "start_time": start_time_joseph.strftime('%H:%M'),
            "end_time": end_time_joseph.strftime('%H:%M'),
        })
        current_time = end_time_joseph

# Lastly, meet Emily
if current_time < meetings["Emily"]["available_end"]:
    travel_time = travel_times[("Richmond District", "Presidio")]
    start_time_emily = max(current_time + timedelta(minutes=travel_time), meetings["Emily"]["available_start"])
    end_time_emily = start_time_emily + timedelta(minutes=meetings["Emily"]["min_duration"])
    
    # Check if meeting with Emily ends before she is unavailable
    if end_time_emily <= meetings["Emily"]["available_end"]:
        itinerary.append({
            "action": "meet",
            "location": "Presidio",
            "person": "Emily",
            "start_time": start_time_emily.strftime('%H:%M'),
            "end_time": end_time_emily.strftime('%H:%M'),
        })

# Output the itinerary in JSON format
output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))