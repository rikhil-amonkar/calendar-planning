import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    "Bayview": {"Nob Hill": 20, "Union Square": 17, "Chinatown": 18, "The Castro": 20, "Presidio": 31, "Pacific Heights": 23, "Russian Hill": 23},
    "Nob Hill": {"Bayview": 19, "Union Square": 7, "Chinatown": 6, "The Castro": 17, "Presidio": 17, "Pacific Heights": 8, "Russian Hill": 5},
    "Union Square": {"Bayview": 15, "Nob Hill": 9, "Chinatown": 7, "The Castro": 19, "Presidio": 24, "Pacific Heights": 15, "Russian Hill": 13},
    "Chinatown": {"Bayview": 22, "Nob Hill": 8, "Union Square": 7, "The Castro": 22, "Presidio": 19, "Pacific Heights": 10, "Russian Hill": 7},
    "The Castro": {"Bayview": 19, "Nob Hill": 16, "Union Square": 19, "Chinatown": 20, "Presidio": 20, "Pacific Heights": 16, "Russian Hill": 18},
    "Presidio": {"Bayview": 31, "Nob Hill": 18, "Union Square": 22, "Chinatown": 21, "The Castro": 21, "Pacific Heights": 11, "Russian Hill": 14},
    "Pacific Heights": {"Bayview": 22, "Nob Hill": 8, "Union Square": 12, "Chinatown": 11, "The Castro": 16, "Presidio": 11, "Russian Hill": 7},
    "Russian Hill": {"Bayview": 23, "Nob Hill": 5, "Union Square": 11, "Chinatown": 9, "The Castro": 21, "Presidio": 14, "Pacific Heights": 7}
}

# Define the meeting constraints
constraints = {
    "Paul": {"location": "Nob Hill", "start_time": "16:15", "end_time": "21:15", "min_duration": 60},
    "Carol": {"location": "Union Square", "start_time": "18:00", "end_time": "20:15", "min_duration": 120},
    "Patricia": {"location": "Chinatown", "start_time": "20:00", "end_time": "21:30", "min_duration": 75},
    "Karen": {"location": "The Castro", "start_time": "17:00", "end_time": "19:00", "min_duration": 45},
    "Nancy": {"location": "Presidio", "start_time": "11:45", "end_time": "22:00", "min_duration": 30},
    "Jeffrey": {"location": "Pacific Heights", "start_time": "20:00", "end_time": "20:45", "min_duration": 45},
    "Matthew": {"location": "Russian Hill", "start_time": "15:45", "end_time": "21:45", "min_duration": 75}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_to_str(time_obj):
    return time_obj.strftime("%H:%M")

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_optimal_schedule():
    current_time = parse_time("9:00")
    current_location = "Bayview"
    itinerary = []

    def add_meeting(person, location, start_time, end_time):
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": time_to_str(start_time),
            "end_time": time_to_str(end_time)
        })

    def try_meeting(person, location, start_time, end_time, min_duration):
        nonlocal current_time, current_location
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + timedelta(minutes=travel_time)
        meeting_start_time = max(arrival_time, start_time)
        meeting_end_time = min(end_time, meeting_start_time + timedelta(minutes=min_duration))
        
        if can_meet(meeting_start_time, meeting_end_time, min_duration):
            add_meeting(person, location, meeting_start_time, meeting_end_time)
            current_time = meeting_end_time
            current_location = location

    # Sort constraints by latest possible start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]["end_time"] - timedelta(minutes=x[1]["min_duration"])))

    for person, details in sorted_constraints:
        try_meeting(person, details["location"], parse_time(details["start_time"]), parse_time(details["end_time"]), details["min_duration"])

    return {"itinerary": itinerary}

# Compute and print the optimal schedule
schedule = find_optimal_schedule()
print(json.dumps(schedule))