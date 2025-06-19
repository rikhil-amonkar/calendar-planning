import json

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

# Hardcoded travel time matrix
travel_matrix = {
    "Russian Hill": {
        "Sunset District": 23, "Union Square": 10, "Nob Hill": 5, "Marina District": 7,
        "Richmond District": 14, "Financial District": 11, "Embarcadero": 8, "The Castro": 21,
        "Alamo Square": 15, "Presidio": 14
    },
    "Sunset District": {
        "Russian Hill": 24, "Union Square": 30, "Nob Hill": 27, "Marina District": 21,
        "Richmond District": 12, "Financial District": 30, "Embarcadero": 30, "The Castro": 17,
        "Alamo Square": 17, "Presidio": 16
    },
    "Union Square": {
        "Russian Hill": 13, "Sunset District": 27, "Nob Hill": 9, "Marina District": 18,
        "Richmond District": 20, "Financial District": 9, "Embarcadero": 11, "The Castro": 17,
        "Alamo Square": 15, "Presidio": 24
    },
    "Nob Hill": {
        "Russian Hill": 5, "Sunset District": 24, "Union Square": 7, "Marina District": 11,
        "Richmond District": 14, "Financial District": 9, "Embarcadero": 9, "The Castro": 17,
        "Alamo Square": 11, "Presidio": 17
    },
    "Marina District": {
        "Russian Hill": 8, "Sunset District": 19, "Union Square": 16, "Nob Hill": 12,
        "Richmond District": 11, "Financial District": 17, "Embarcadero": 14, "The Castro": 22,
        "Alamo Square": 15, "Presidio": 10
    },
    "Richmond District": {
        "Russian Hill": 13, "Sunset District": 11, "Union Square": 21, "Nob Hill": 17,
        "Marina District": 9, "Financial District": 22, "Embarcadero": 19, "The Castro": 16,
        "Alamo Square": 13, "Presidio": 7
    },
    "Financial District": {
        "Russian Hill": 11, "Sunset District": 30, "Union Square": 9, "Nob Hill": 8,
        "Marina District": 15, "Richmond District": 21, "Embarcadero": 4, "The Castro": 20,
        "Alamo Square": 17, "Presidio": 22
    },
    "Embarcadero": {
        "Russian Hill": 8, "Sunset District": 30, "Union Square": 10, "Nob Hill": 10,
        "Marina District": 12, "Richmond District": 21, "Financial District": 5, "The Castro": 25,
        "Alamo Square": 19, "Presidio": 20
    },
    "The Castro": {
        "Russian Hill": 18, "Sunset District": 17, "Union Square": 19, "Nob Hill": 16,
        "Marina District": 21, "Richmond District": 16, "Financial District": 21, "Embarcadero": 22,
        "Alamo Square": 8, "Presidio": 20
    },
    "Alamo Square": {
        "Russian Hill": 13, "Sunset District": 16, "Union Square": 14, "Nob Hill": 11,
        "Marina District": 15, "Richmond District": 11, "Financial District": 17, "Embarcadero": 16,
        "The Castro": 8, "Presidio": 17
    },
    "Presidio": {
        "Russian Hill": 14, "Sunset District": 15, "Union Square": 22, "Nob Hill": 18,
        "Marina District": 11, "Richmond District": 7, "Financial District": 23, "Embarcadero": 20,
        "The Castro": 21, "Alamo Square": 19
    }
}

# Define the meetings in the order we want to schedule them
meetings_in_order = [
    ("William", "Presidio", 7*60, 12*60+45, 60),
    ("Kimberly", "Alamo Square", 9*60, 14*60+30, 105),
    ("George", "The Castro", 14*60+15, 19*60, 105),
    ("Patricia", "Nob Hill", 15*60, 19*60+15, 120),
    ("Charles", "Richmond District", 17*60+15, 21*60, 15),
    ("Ronald", "Embarcadero", 18*60+15, 20*60+45, 30),
    ("David", "Sunset District", 9*60+15, 22*60, 15),
    ("Kenneth", "Union Square", 21*60+15, 21*60+45, 15)
]

# Start at Russian Hill at 9:00 AM (540 minutes)
current_time = 540
previous_location = "Russian Hill"
itinerary = []

for meeting in meetings_in_order:
    person, location, avail_start, avail_end, min_duration = meeting
    travel_time = travel_matrix[previous_location][location]
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, avail_start)
    end_time = start_time + min_duration
    if end_time > avail_end:
        break
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": minutes_to_time(start_time),
        "end_time": minutes_to_time(end_time)
    })
    current_time = end_time
    previous_location = location

output = {"itinerary": itinerary}
print(json.dumps(output))