import json
from datetime import datetime, timedelta

# Travel times in minutes
travel_times = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Union Square"): 11,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Golden Gate Park"): 18,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Golden Gate Park"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Union Square"): 22,
}

# Meeting constraints
constraints = {
    "Karen": {"location": "Russian Hill", "start": "21:45", "end": "22:45", "duration": 60},
    "Jessica": {"location": "The Castro", "start": "15:45", "end": "19:30", "duration": 60},
    "Matthew": {"location": "Richmond District", "start": "07:30", "end": "15:15", "duration": 15},
    "Michelle": {"location": "Marina District", "start": "10:30", "end": "18:45", "duration": 75},
    "Carol": {"location": "North Beach", "start": "12:00", "end": "17:00", "duration": 90},
    "Stephanie": {"location": "Union Square", "start": "10:45", "end": "14:15", "duration": 30},
    "Linda": {"location": "Golden Gate Park", "start": "10:45", "end": "22:00", "duration": 90},
}

# Starting time
arrival_time = datetime.strptime("09:00", "%H:%M")

# Resulting itinerary
itinerary = []

# Meeting strategy
def book_meeting(person, location, start_time, duration):
    end_time = start_time + timedelta(minutes=duration)
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": start_time.strftime("%H:%M"),
        "end_time": end_time.strftime("%H:%M"),
    })
    return end_time

# Schedule the meetings based on constraints
start_time = arrival_time

# Meet Matthew
if start_time < datetime.strptime(constraints["Matthew"]["end"], "%H:%M"):
    travel_time = travel_times[("Sunset District", "Richmond District")]
    start_time += timedelta(minutes=travel_time)
    book_meeting("Matthew", "Richmond District", start_time, constraints["Matthew"]["duration"])
    start_time += timedelta(minutes=constraints["Matthew"]["duration"])

# Meet Stephanie
if start_time < datetime.strptime(constraints["Stephanie"]["end"], "%H:%M"):
    travel_time = travel_times[("Richmond District", "Union Square")]
    start_time += timedelta(minutes=travel_time)
    book_meeting("Stephanie", "Union Square", start_time, constraints["Stephanie"]["duration"])
    start_time += timedelta(minutes=constraints["Stephanie"]["duration"])

# Meet Michelle
if start_time < datetime.strptime(constraints["Michelle"]["end"], "%H:%M"):
    travel_time = travel_times[("Union Square", "Marina District")]
    start_time += timedelta(minutes=travel_time)
    book_meeting("Michelle", "Marina District", start_time, constraints["Michelle"]["duration"])
    start_time += timedelta(minutes=constraints["Michelle"]["duration"])

# Meet Carol
if start_time < datetime.strptime(constraints["Carol"]["end"], "%H:%M"):
    travel_time = travel_times[("Marina District", "North Beach")]
    start_time += timedelta(minutes=travel_time)
    book_meeting("Carol", "North Beach", start_time, constraints["Carol"]["duration"])
    start_time += timedelta(minutes=constraints["Carol"]["duration"])

# Meet Jessica
if start_time < datetime.strptime(constraints["Jessica"]["end"], "%H:%M"):
    travel_time = travel_times[("North Beach", "The Castro")]
    start_time += timedelta(minutes=travel_time)
    book_meeting("Jessica", "The Castro", start_time, constraints["Jessica"]["duration"])
    start_time += timedelta(minutes=constraints["Jessica"]["duration"])

# Meet Linda
if start_time < datetime.strptime(constraints["Linda"]["end"], "%H:%M"):
    travel_time = travel_times[("The Castro", "Golden Gate Park")]
    start_time += timedelta(minutes=travel_time)
    book_meeting("Linda", "Golden Gate Park", start_time, constraints["Linda"]["duration"])
    start_time += timedelta(minutes=constraints["Linda"]["duration"])

# Meet Karen
if start_time < datetime.strptime(constraints["Karen"]["end"], "%H:%M"):
    travel_time = travel_times[("Golden Gate Park", "Russian Hill")]
    start_time += timedelta(minutes=travel_time)
    start_time = datetime.strptime(constraints["Karen"]["start"], "%H:%M")  # Align with Karen's time
    book_meeting("Karen", "Russian Hill", start_time, constraints["Karen"]["duration"])

# Output the JSON result
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))