import json
from datetime import datetime, timedelta

# Define travel times in a minutes dictionary
travel_times = {
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Marina District"): 18,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Marina District"): 11,
    ("Haight-Ashbury", "Union Square"): 17,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Nob Hill"): 8,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Marina District"): 12,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Chinatown"): 16
}

# Define meeting constraints
constraints = {
    "Karen": {"location": "Nob Hill", "available_from": "21:15", "available_to": "21:45", "duration": 30},
    "Joseph": {"location": "Haight-Ashbury", "available_from": "12:30", "available_to": "19:45", "duration": 90},
    "Sandra": {"location": "Chinatown", "available_from": "07:15", "available_to": "19:15", "duration": 75},
    "Nancy": {"location": "Marina District", "available_from": "11:00", "available_to": "20:15", "duration": 105}
}

# Define start time at Union Square
start_time = datetime.strptime("09:00", "%H:%M")

# Function to convert string to datetime
def str_to_time(s):
    return datetime.strptime(s, "%H:%M")

# Function to create a meeting schedule
def create_schedule():
    schedule = []
    current_time = start_time

    # Meet Sandra
    sandra_start = max(str_to_time(constraints["Sandra"]["available_from"]), current_time)
    sandra_end = sandra_start + timedelta(minutes=constraints["Sandra"]["duration"])
    if sandra_end <= str_to_time(constraints["Sandra"]["available_to"]):
        schedule.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "Sandra",
            "start_time": sandra_start.strftime("%H:%M"),
            "end_time": sandra_end.strftime("%H:%M")
        })
        current_time = sandra_end + timedelta(minutes=travel_times[("Chinatown", "Marina District")])

    # Meet Nancy
    nancy_start = max(str_to_time(constraints["Nancy"]["available_from"]), current_time)
    nancy_end = nancy_start + timedelta(minutes=constraints["Nancy"]["duration"])
    if nancy_end <= str_to_time(constraints["Nancy"]["available_to"]):
        schedule.append({
            "action": "meet",
            "location": "Marina District",
            "person": "Nancy",
            "start_time": nancy_start.strftime("%H:%M"),
            "end_time": nancy_end.strftime("%H:%M")
        })
        current_time = nancy_end + timedelta(minutes=travel_times[("Marina District", "Nob Hill")])

    # Meet Karen
    karen_start = max(str_to_time(constraints["Karen"]["available_from"]), current_time)
    karen_end = karen_start + timedelta(minutes=constraints["Karen"]["duration"])
    if karen_end <= str_to_time(constraints["Karen"]["available_to"]):
        schedule.append({
            "action": "meet",
            "location": "Nob Hill",
            "person": "Karen",
            "start_time": karen_start.strftime("%H:%M"),
            "end_time": karen_end.strftime("%H:%M")
        })
        current_time = karen_end + timedelta(minutes=travel_times[("Nob Hill", "Haight-Ashbury")])

    # Meet Joseph
    joseph_start = max(str_to_time(constraints["Joseph"]["available_from"]), current_time)
    joseph_end = joseph_start + timedelta(minutes=constraints["Joseph"]["duration"])
    if joseph_end <= str_to_time(constraints["Joseph"]["available_to"]):
        schedule.append({
            "action": "meet",
            "location": "Haight-Ashbury",
            "person": "Joseph",
            "start_time": joseph_start.strftime("%H:%M"),
            "end_time": joseph_end.strftime("%H:%M")
        })

    return {
        "itinerary": schedule
    }

# Generate the schedule and print it as JSON
optimal_schedule = create_schedule()
print(json.dumps(optimal_schedule, indent=2))