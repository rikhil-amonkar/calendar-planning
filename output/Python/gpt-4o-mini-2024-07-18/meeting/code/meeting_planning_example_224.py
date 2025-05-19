import json
from datetime import datetime, timedelta

# Travel times between locations in minutes
travel_times = {
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Presidio"): 7,
}

# Constraints for meeting
friends = {
    "Melissa": {
        "location": "Golden Gate Park",
        "start": "08:30",
        "end": "20:00",
        "min_duration": 15
    },
    "Nancy": {
        "location": "Presidio",
        "start": "19:45",
        "end": "22:00",
        "min_duration": 105
    },
    "Emily": {
        "location": "Richmond District",
        "start": "16:45",
        "end": "22:00",
        "min_duration": 120
    }
}

arrival_time = "09:00"
arrival_datetime = datetime.strptime(arrival_time, "%H:%M")

# Find the optimal schedule
itinerary = []

# Meeting with Melissa
melissa_start = max(arrival_datetime + timedelta(minutes=travel_times[("Fisherman's Wharf", "Golden Gate Park")]), 
                    datetime.strptime(friends["Melissa"]["start"], "%H:%M"))
melissa_end = melissa_start + timedelta(minutes=friends["Melissa"]["min_duration"])

if melissa_end <= datetime.strptime(friends["Melissa"]["end"], "%H:%M"):
    itinerary.append({
        "action": "meet",
        "location": "Golden Gate Park",
        "person": "Melissa",
        "start_time": melissa_start.strftime("%H:%M"),
        "end_time": melissa_end.strftime("%H:%M")
    })

# Meeting with Emily
travel_time_to_emily = travel_times[("Fisherman's Wharf", "Richmond District")]
departure_after_melissa = melissa_end + timedelta(minutes=travel_time_to_emily)
emily_start = max(departure_after_melissa, 
                  datetime.strptime(friends["Emily"]["start"], "%H:%M"))
emily_end = emily_start + timedelta(minutes=friends["Emily"]["min_duration"])

if emily_end <= datetime.strptime(friends["Emily"]["end"], "%H:%M"):
    itinerary.append({
        "action": "meet",
        "location": "Richmond District",
        "person": "Emily",
        "start_time": emily_start.strftime("%H:%M"),
        "end_time": emily_end.strftime("%H:%M")
    })

# Meeting with Nancy
travel_time_to_nancy = travel_times[("Richmond District", "Presidio")]
departure_after_emily = emily_end + timedelta(minutes=travel_time_to_nancy)
nancy_start = max(departure_after_emily, 
                  datetime.strptime(friends["Nancy"]["start"], "%H:%M"))
nancy_end = nancy_start + timedelta(minutes=friends["Nancy"]["min_duration"])

if nancy_end <= datetime.strptime(friends["Nancy"]["end"], "%H:%M"):
    itinerary.append({
        "action": "meet",
        "location": "Presidio",
        "person": "Nancy",
        "start_time": nancy_start.strftime("%H:%M"),
        "end_time": nancy_end.strftime("%H:%M")
    })

# Output the itinerary in JSON format
output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))