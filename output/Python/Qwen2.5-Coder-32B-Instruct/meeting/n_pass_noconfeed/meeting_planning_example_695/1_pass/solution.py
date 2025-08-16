import json
from datetime import datetime, timedelta

# Define travel times
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

# Define meeting constraints
constraints = {
    "Paul": {"location": "Nob Hill", "start": "16:15", "end": "21:15", "min_duration": 60},
    "Carol": {"location": "Union Square", "start": "18:00", "end": "20:15", "min_duration": 120},
    "Patricia": {"location": "Chinatown", "start": "20:00", "end": "21:30", "min_duration": 75},
    "Karen": {"location": "The Castro", "start": "17:00", "end": "19:00", "min_duration": 45},
    "Nancy": {"location": "Presidio", "start": "11:45", "end": "22:00", "min_duration": 30},
    "Jeffrey": {"location": "Pacific Heights", "start": "20:00", "end": "20:45", "min_duration": 45},
    "Matthew": {"location": "Russian Hill", "start": "15:45", "end": "21:45", "min_duration": 75}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M")

def can_meet(start, end, min_duration):
    duration = (parse_time(end) - parse_time(start)).seconds // 60
    return duration >= min_duration

def find_schedule():
    current_location = "Bayview"
    current_time = parse_time("9:00")
    itinerary = []

    def add_meeting(person, location, start, end):
        nonlocal current_time, current_location
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + timedelta(minutes=travel_time)
        if arrival_time < parse_time(start):
            current_time = arrival_time
        else:
            current_time = parse_time(start)
        meeting_start = current_time
        meeting_end = parse_time(end)
        if can_meet(format_time(meeting_start), format_time(meeting_end), constraints[person]["min_duration"]):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(meeting_start),
                "end_time": format_time(min(meeting_start + timedelta(minutes=constraints[person]["min_duration"]), meeting_end))
            })
            current_time = meeting_start + timedelta(minutes=constraints[person]["min_duration"])
            current_location = location

    # Prioritize meetings based on constraints
    add_meeting("Nancy", "Presidio", "11:45", "22:00")
    add_meeting("Karen", "The Castro", "17:00", "19:00")
    add_meeting("Matthew", "Russian Hill", "15:45", "21:45")
    add_meeting("Paul", "Nob Hill", "16:15", "21:15")
    add_meeting("Carol", "Union Square", "18:00", "20:15")
    add_meeting("Jeffrey", "Pacific Heights", "20:00", "20:45")
    add_meeting("Patricia", "Chinatown", "20:00", "21:30")

    return {"itinerary": itinerary}

schedule = find_schedule()
print(json.dumps(schedule))