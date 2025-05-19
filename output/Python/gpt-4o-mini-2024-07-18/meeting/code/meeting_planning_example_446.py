import json
from datetime import datetime, timedelta

# Define travel times in a dictionary
travel_times = {
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Bayview"): 26,
    ("Richmond District", "Union Square"): 21,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Chinatown"): 16,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Union Square"): 16,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "Union Square"): 7,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Union Square"): 9,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Marina District"): 25,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Union Square"): 17,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Bayview"): 15,
}

# Define meeting constraints
constraints = {
    "Kimberly": {"location": "Marina District", "available": (datetime.strptime("13:15", "%H:%M"), datetime.strptime("16:45", "%H:%M")), "duration": timedelta(minutes=15)},
    "Robert": {"location": "Chinatown", "available": (datetime.strptime("12:15", "%H:%M"), datetime.strptime("20:15", "%H:%M")), "duration": timedelta(minutes=15)},
    "Rebecca": {"location": "Financial District", "available": (datetime.strptime("13:15", "%H:%M"), datetime.strptime("16:45", "%H:%M")), "duration": timedelta(minutes=75)},
    "Margaret": {"location": "Bayview", "available": (datetime.strptime("9:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")), "duration": timedelta(minutes=30)},
    "Kenneth": {"location": "Union Square", "available": (datetime.strptime("19:30", "%H:%M"), datetime.strptime("21:15", "%H:%M")), "duration": timedelta(minutes=75)},
}

# Initialize meeting schedule
itinerary = []
start_time = datetime.strptime("09:00", "%H:%M")

# Function to add meeting to the itinerary
def add_meeting(person, location, start, duration):
    end = start + duration
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": start.strftime("%H:%M"),
        "end_time": end.strftime("%H:%M"),
    })
    return end

# Schedule meetings
current_time = start_time
current_location = "Richmond District"

# Meeting with Margaret first
if current_time < constraints["Margaret"]["available"][1]:
    travel_time = travel_times[(current_location, "Bayview")]
    current_time += timedelta(minutes=travel_time)
    if current_time < constraints["Margaret"]["available"][1]:
        meeting_start = max(current_time, constraints["Margaret"]["available"][0])
        current_time = add_meeting("Margaret", "Bayview", meeting_start, constraints["Margaret"]["duration"])
        current_location = "Bayview"

# Meeting with Robert
if current_time < constraints["Robert"]["available"][1]:
    travel_time = travel_times[(current_location, "Chinatown")]
    current_time += timedelta(minutes=travel_time)
    if current_time < constraints["Robert"]["available"][1]:
        meeting_start = max(current_time, constraints["Robert"]["available"][0])
        current_time = add_meeting("Robert", "Chinatown", meeting_start, constraints["Robert"]["duration"])
        current_location = "Chinatown"

# Meeting with Kimberly
if current_time < constraints["Kimberly"]["available"][1]:
    travel_time = travel_times[(current_location, "Marina District")]
    current_time += timedelta(minutes=travel_time)
    if current_time < constraints["Kimberly"]["available"][1]:
        meeting_start = max(current_time, constraints["Kimberly"]["available"][0])
        current_time = add_meeting("Kimberly", "Marina District", meeting_start, constraints["Kimberly"]["duration"])
        current_location = "Marina District"

# Meeting with Rebecca
if current_time < constraints["Rebecca"]["available"][1]:
    travel_time = travel_times[(current_location, "Financial District")]
    current_time += timedelta(minutes=travel_time)
    if current_time < constraints["Rebecca"]["available"][1]:
        meeting_start = max(current_time, constraints["Rebecca"]["available"][0])
        current_time = add_meeting("Rebecca", "Financial District", meeting_start, constraints["Rebecca"]["duration"])
        current_location = "Financial District"

# Meeting with Kenneth
if current_time < constraints["Kenneth"]["available"][1]:
    travel_time = travel_times[(current_location, "Union Square")]
    current_time += timedelta(minutes=travel_time)
    if current_time < constraints["Kenneth"]["available"][1]:
        meeting_start = max(current_time, constraints["Kenneth"]["available"][0])
        current_time = add_meeting("Kenneth", "Union Square", meeting_start, constraints["Kenneth"]["duration"])
        current_location = "Union Square"

# Convert the itinerary to JSON
output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))