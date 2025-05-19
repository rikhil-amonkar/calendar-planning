import json
from datetime import datetime, timedelta

# Travel times in minutes
travel_times = {
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "Bayview"): 26,
}

# Meeting constraints
constraints = {
    "Nancy": {"location": "Chinatown", "available_from": "9:30", "available_to": "13:30", "min_duration": 90},
    "Mary": {"location": "Alamo Square", "available_from": "7:00", "available_to": "21:00", "min_duration": 75},
    "Jessica": {"location": "Bayview", "available_from": "11:15", "available_to": "13:45", "min_duration": 45},
    "Rebecca": {"location": "Fisherman's Wharf", "available_from": "7:00", "available_to": "8:30", "min_duration": 45},
}

# Start time
arrival_time = datetime.strptime('09:00', '%H:%M')

# Function to calculate meeting time
def schedule_meeting(start, duration):
    end = start + timedelta(minutes=duration)
    return start, end

# List to hold the itinerary
itinerary = []

# Meeting with Rebecca
rebecca_start = datetime.strptime(constraints["Rebecca"]["available_from"], '%H:%M')
rebecca_end = datetime.strptime(constraints["Rebecca"]["available_to"], '%H:%M')
if rebecca_end >= arrival_time + timedelta(minutes=10):
    rebecca_meet_start = max(rebecca_start, arrival_time + timedelta(minutes=10))
    rebecca_meet_end = rebecca_meet_start + timedelta(minutes=constraints["Rebecca"]["min_duration"])
    itinerary.append({
        "action": "meet",
        "location": "Fisherman's Wharf",
        "person": "Rebecca",
        "start_time": rebecca_meet_start.strftime('%H:%M'),
        "end_time": rebecca_meet_end.strftime('%H:%M')
    })
    travel_to_chinatown = travel_times[("Fisherman's Wharf", "Chinatown")]
    arrival_time = rebecca_meet_end + timedelta(minutes=travel_to_chinatown)

# Meeting with Nancy
nancy_start = datetime.strptime(constraints["Nancy"]["available_from"], '%H:%M')
nancy_end = datetime.strptime(constraints["Nancy"]["available_to"], '%H:%M')
if arrival_time < nancy_end and arrival_time + timedelta(minutes=constraints["Nancy"]["min_duration"]) <= nancy_end:
    nancy_meet_start = max(arrival_time, nancy_start)
    nancy_meet_end = nancy_meet_start + timedelta(minutes=constraints["Nancy"]["min_duration"])
    itinerary.append({
        "action": "meet",
        "location": "Chinatown",
        "person": "Nancy",
        "start_time": nancy_meet_start.strftime('%H:%M'),
        "end_time": nancy_meet_end.strftime('%H:%M')
    })
    travel_to_alamo_square = travel_times[("Chinatown", "Alamo Square")]
    arrival_time = nancy_meet_end + timedelta(minutes=travel_to_alamo_square)

# Meeting with Mary
mary_start = datetime.strptime(constraints["Mary"]["available_from"], '%H:%M')
mary_end = datetime.strptime(constraints["Mary"]["available_to"], '%H:%M')
if arrival_time < mary_end and arrival_time + timedelta(minutes=constraints["Mary"]["min_duration"]) <= mary_end:
    mary_meet_start = max(arrival_time, mary_start)
    mary_meet_end = mary_meet_start + timedelta(minutes=constraints["Mary"]["min_duration"])
    itinerary.append({
        "action": "meet",
        "location": "Alamo Square",
        "person": "Mary",
        "start_time": mary_meet_start.strftime('%H:%M'),
        "end_time": mary_meet_end.strftime('%H:%M')
    })
    travel_to_bayview = travel_times[("Alamo Square", "Bayview")]
    arrival_time = mary_meet_end + timedelta(minutes=travel_to_bayview)

# Meeting with Jessica
jessica_start = datetime.strptime(constraints["Jessica"]["available_from"], '%H:%M')
jessica_end = datetime.strptime(constraints["Jessica"]["available_to"], '%H:%M')
if arrival_time < jessica_end and arrival_time + timedelta(minutes=constraints["Jessica"]["min_duration"]) <= jessica_end:
    jessica_meet_start = max(arrival_time, jessica_start)
    jessica_meet_end = jessica_meet_start + timedelta(minutes=constraints["Jessica"]["min_duration"])
    itinerary.append({
        "action": "meet",
        "location": "Bayview",
        "person": "Jessica",
        "start_time": jessica_meet_start.strftime('%H:%M'),
        "end_time": jessica_meet_end.strftime('%H:%M')
    })

# Output the resulting itinerary as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))