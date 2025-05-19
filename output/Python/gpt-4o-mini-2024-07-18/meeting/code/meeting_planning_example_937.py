import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    "Russian Hill": {
        "Sunset District": 23,
        "Union Square": 10,
        "Nob Hill": 5,
        "Marina District": 7,
        "Richmond District": 14,
        "Financial District": 11,
        "Embarcadero": 8,
        "The Castro": 21,
        "Alamo Square": 15,
        "Presidio": 14
    },
    "Sunset District": {
        "Russian Hill": 24,
        "Union Square": 30,
        "Nob Hill": 27,
        "Marina District": 21,
        "Richmond District": 12,
        "Financial District": 30,
        "Embarcadero": 30,
        "The Castro": 17,
        "Alamo Square": 17,
        "Presidio": 16
    },
    "Union Square": {
        "Russian Hill": 13,
        "Sunset District": 27,
        "Nob Hill": 9,
        "Marina District": 18,
        "Richmond District": 20,
        "Financial District": 9,
        "Embarcadero": 11,
        "The Castro": 17,
        "Alamo Square": 15,
        "Presidio": 24
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Sunset District": 24,
        "Union Square": 7,
        "Marina District": 11,
        "Richmond District": 14,
        "Financial District": 9,
        "Embarcadero": 9,
        "The Castro": 17,
        "Alamo Square": 11,
        "Presidio": 17
    },
    "Marina District": {
        "Russian Hill": 8,
        "Sunset District": 19,
        "Union Square": 16,
        "Nob Hill": 12,
        "Richmond District": 11,
        "Financial District": 17,
        "Embarcadero": 14,
        "The Castro": 22,
        "Alamo Square": 15,
        "Presidio": 10
    },
    "Richmond District": {
        "Russian Hill": 13,
        "Sunset District": 11,
        "Union Square": 21,
        "Nob Hill": 17,
        "Marina District": 9,
        "Financial District": 22,
        "Embarcadero": 19,
        "The Castro": 16,
        "Alamo Square": 13,
        "Presidio": 7
    },
    "Financial District": {
        "Russian Hill": 11,
        "Sunset District": 30,
        "Union Square": 9,
        "Nob Hill": 8,
        "Marina District": 15,
        "Richmond District": 21,
        "Embarcadero": 4,
        "The Castro": 20,
        "Alamo Square": 17,
        "Presidio": 22
    },
    "Embarcadero": {
        "Russian Hill": 8,
        "Sunset District": 30,
        "Union Square": 10,
        "Nob Hill": 10,
        "Marina District": 12,
        "Richmond District": 21,
        "Financial District": 5,
        "The Castro": 25,
        "Alamo Square": 19,
        "Presidio": 20
    },
    "The Castro": {
        "Russian Hill": 18,
        "Sunset District": 17,
        "Union Square": 19,
        "Nob Hill": 16,
        "Marina District": 21,
        "Richmond District": 16,
        "Financial District": 21,
        "Embarcadero": 22,
        "Alamo Square": 8,
        "Presidio": 20
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Sunset District": 16,
        "Union Square": 14,
        "Nob Hill": 11,
        "Marina District": 15,
        "Richmond District": 11,
        "Financial District": 17,
        "Embarcadero": 16,
        "The Castro": 8,
        "Presidio": 17
    },
    "Presidio": {
        "Russian Hill": 14,
        "Sunset District": 15,
        "Union Square": 22,
        "Nob Hill": 18,
        "Marina District": 11,
        "Richmond District": 7,
        "Financial District": 23,
        "Embarcadero": 20,
        "The Castro": 21,
        "Alamo Square": 19
    }
}

# Meeting constraints (tuple of (start_time, end_time, duration, location, person))
meetings = [
    (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M"), 15, "Sunset District", "David"),
    (datetime.strptime("09:15", "%H:%M"), datetime.strptime("09:45", "%H:%M"), 15, "Union Square", "Kenneth"),
    (datetime.strptime("15:00", "%H:%M"), datetime.strptime("19:15", "%H:%M"), 120, "Nob Hill", "Patricia"),
    (datetime.strptime("14:45", "%H:%M"), datetime.strptime("16:45", "%H:%M"), 45, "Marina District", "Mary"),
    (datetime.strptime("17:15", "%H:%M"), datetime.strptime("21:00", "%H:%M"), 15, "Richmond District", "Charles"),
    (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:15", "%H:%M"), 90, "Financial District", "Joshua"),
    (datetime.strptime("18:15", "%H:%M"), datetime.strptime("20:45", "%H:%M"), 30, "Embarcadero", "Ronald"),
    (datetime.strptime("14:15", "%H:%M"), datetime.strptime("19:00", "%H:%M"), 105, "The Castro", "George"),
    (datetime.strptime("09:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"), 105, "Alamo Square", "Kimberly"),
    (datetime.strptime("07:00", "%H:%M"), datetime.strptime("12:45", "%H:%M"), 60, "Presidio", "William"),
]

# Start simulation at Russian Hill at 9:00 AM
current_time = datetime.strptime("09:00", "%H:%M")
itinerary = []

# Helper function to format time in 24-hour format
def format_time(dt):
    return dt.strftime("%H:%M")

# Helper function to meet
def schedule_meeting(start_time, end_time, location, person):
    global current_time, itinerary
    travel_time = travel_times["Russian Hill"].get(location, 0) if current_time == datetime.strptime("09:00", "%H:%M") else travel_times[last_location].get(location, 0)
    if current_time + timedelta(minutes=travel_time) <= start_time:
        travel_time_needed = travel_times["Russian Hill"].get(location, 0)
        end_time = max(end_time, start_time + timedelta(minutes=15))
        
        current_time += timedelta(minutes=travel_time + (start_time - current_time).seconds // 60)
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": format_time(current_time),
            "end_time": format_time(end_time)
        })
        
        current_time = end_time
        return True
    return False

# Iterate through meetings to find suitable schedule
last_location = "Russian Hill"
for meeting in meetings:
    start_time, end_time, duration, location, person = meeting
    end_time = start_time + timedelta(minutes=duration)
    
    if schedule_meeting(start_time, end_time, location, person):
        last_location = location

# Output the result as a JSON-formatted dictionary
result = {
    "itinerary": itinerary
}

print(json.dumps(result, indent=2))