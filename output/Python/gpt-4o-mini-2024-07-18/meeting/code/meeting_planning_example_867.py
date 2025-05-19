import json
from datetime import datetime, timedelta

# Travel times in minutes
travel_times = {
    "Haight-Ashbury": {
        "Mission District": 12,
        "Union Square": 18,
        "Pacific Heights": 11,
        "Bayview": 19,
        "Fisherman's Wharf": 22,
        "Marina District": 16,
        "Richmond District": 10,
        "Sunset District": 15,
        "Golden Gate Park": 7,
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Union Square": 14,
        "Pacific Heights": 15,
        "Bayview": 13,
        "Fisherman's Wharf": 22,
        "Marina District": 20,
        "Richmond District": 20,
        "Sunset District": 24,
        "Golden Gate Park": 17,
    },
    "Union Square": {
        "Haight-Ashbury": 18,
        "Mission District": 14,
        "Pacific Heights": 12,
        "Bayview": 18,
        "Fisherman's Wharf": 13,
        "Marina District": 16,
        "Richmond District": 21,
        "Sunset District": 30,
        "Golden Gate Park": 22,
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Union Square": 12,
        "Bayview": 23,
        "Fisherman's Wharf": 12,
        "Marina District": 7,
        "Richmond District": 10,
        "Sunset District": 21,
        "Golden Gate Park": 15,
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Union Square": 18,
        "Pacific Heights": 23,
        "Fisherman's Wharf": 26,
        "Marina District": 27,
        "Richmond District": 27,
        "Sunset District": 22,
        "Golden Gate Park": 22,
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Union Square": 13,
        "Pacific Heights": 12,
        "Bayview": 26,
        "Marina District": 10,
        "Richmond District": 18,
        "Sunset District": 29,
        "Golden Gate Park": 25,
    },
    "Marina District": {
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Union Square": 16,
        "Pacific Heights": 7,
        "Bayview": 27,
        "Fisherman's Wharf": 10,
        "Richmond District": 11,
        "Sunset District": 19,
        "Golden Gate Park": 18,
    },
    "Richmond District": {
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Union Square": 21,
        "Pacific Heights": 10,
        "Bayview": 27,
        "Fisherman's Wharf": 18,
        "Marina District": 9,
        "Sunset District": 12,
        "Golden Gate Park": 9,
    },
    "Sunset District": {
        "Haight-Ashbury": 15,
        "Mission District": 25,
        "Union Square": 30,
        "Pacific Heights": 21,
        "Bayview": 22,
        "Fisherman's Wharf": 29,
        "Marina District": 21,
        "Richmond District": 12,
        "Golden Gate Park": 11,
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Mission District": 17,
        "Union Square": 22,
        "Pacific Heights": 15,
        "Bayview": 23,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Richmond District": 7,
        "Sunset District": 10,
    },
}

# Constraints
constraints = {
    "Elizabeth": {"location": "Mission District", "start": "10:30", "end": "20:00", "duration": 90},
    "David": {"location": "Union Square", "start": "15:15", "end": "19:00", "duration": 45},
    "Sandra": {"location": "Pacific Heights", "start": "07:00", "end": "20:00", "duration": 120},
    "Thomas": {"location": "Bayview", "start": "19:30", "end": "20:30", "duration": 30},
    "Robert": {"location": "Fisherman's Wharf", "start": "10:00", "end": "15:00", "duration": 15},
    "Kenneth": {"location": "Marina District", "start": "10:45", "end": "13:00", "duration": 45},
    "Melissa": {"location": "Richmond District", "start": "18:15", "end": "20:00", "duration": 15},
    "Kimberly": {"location": "Sunset District", "start": "10:15", "end": "18:15", "duration": 105},
    "Amanda": {"location": "Golden Gate Park", "start": "07:45", "end": "18:45", "duration": 15},
}

# Function to convert string time to datetime object
def to_time_obj(time_str):
    return datetime.strptime(time_str, "%H:%M")

# Function to convert datetime object to string
def to_time_str(time_obj):
    return time_obj.strftime("%H:%M")

# Initialize the itinerary
itinerary = []

# Calculate schedule
available_time = to_time_obj("09:00")

# Helper function to meet a person
def schedule_meeting(person, location, duration):
    global available_time
    start_meeting = available_time + timedelta(minutes=travel_times["Haight-Ashbury"][location])
    end_meeting = start_meeting + timedelta(minutes=duration)
    if end_meeting.time() <= to_time_obj(constraints[person]["end"]).time():
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": to_time_str(start_meeting),
            "end_time": to_time_str(end_meeting),
        })
        available_time = end_meeting + timedelta(minutes=travel_times[location]["Haight-Ashbury"])

# Meeting schedule
# Meeting Sandra first
schedule_meeting("Sandra", "Pacific Heights", constraints["Sandra"]["duration"])

# Meeting Robert next
schedule_meeting("Robert", "Fisherman's Wharf", constraints["Robert"]["duration"])

# Meeting Kenneth next
schedule_meeting("Kenneth", "Marina District", constraints["Kenneth"]["duration"])

# Meeting Elizabeth next
schedule_meeting("Elizabeth", "Mission District", constraints["Elizabeth"]["duration"])

# Meeting David next
schedule_meeting("David", "Union Square", constraints["David"]["duration"])

# Meeting Kimberly next
schedule_meeting("Kimberly", "Sunset District", constraints["Kimberly"]["duration"])

# Meeting Melissa last
schedule_meeting("Melissa", "Richmond District", constraints["Melissa"]["duration"])

# Meeting Thomas
schedule_meeting("Thomas", "Bayview", constraints["Thomas"]["duration"])

# Prepare output
result = {
    "itinerary": itinerary
}

# Print result as JSON
print(json.dumps(result, indent=2))