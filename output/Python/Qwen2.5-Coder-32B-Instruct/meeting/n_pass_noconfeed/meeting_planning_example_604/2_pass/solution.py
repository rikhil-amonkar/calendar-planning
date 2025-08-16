import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Fisherman's Wharf": {
        "The Castro": 26, "Golden Gate Park": 25, "Embarcadero": 8, "Russian Hill": 7, "Nob Hill": 11, "Alamo Square": 20, "North Beach": 6
    },
    "The Castro": {
        "Fisherman's Wharf": 24, "Golden Gate Park": 11, "Embarcadero": 22, "Russian Hill": 18, "Nob Hill": 16, "Alamo Square": 8, "North Beach": 20
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24, "The Castro": 13, "Embarcadero": 25, "Russian Hill": 19, "Nob Hill": 20, "Alamo Square": 10, "North Beach": 24
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6, "The Castro": 25, "Golden Gate Park": 25, "Russian Hill": 8, "Nob Hill": 10, "Alamo Square": 19, "North Beach": 5
    },
    "Russian Hill": {
        "Fisherman's Wharf": 7, "The Castro": 21, "Golden Gate Park": 21, "Embarcadero": 8, "Nob Hill": 5, "Alamo Square": 15, "North Beach": 5
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11, "The Castro": 17, "Golden Gate Park": 17, "Embarcadero": 9, "Russian Hill": 5, "Alamo Square": 11, "North Beach": 8
    },
    "Alamo Square": {
        "Fisherman's Wharf": 19, "The Castro": 8, "Golden Gate Park": 9, "Embarcadero": 17, "Russian Hill": 13, "Nob Hill": 11, "North Beach": 15
    },
    "North Beach": {
        "Fisherman's Wharf": 5, "The Castro": 22, "Golden Gate Park": 22, "Embarcadero": 6, "Russian Hill": 4, "Nob Hill": 7, "Alamo Square": 16
    }
}

# Define constraints
constraints = {
    "Laura": {"location": "The Castro", "start": "19:45", "end": "21:30", "min_duration": 105},
    "Daniel": {"location": "Golden Gate Park", "start": "21:15", "end": "21:45", "min_duration": 15},
    "William": {"location": "Embarcadero", "start": "7:00", "end": "9:00", "min_duration": 90},
    "Karen": {"location": "Russian Hill", "start": "14:30", "end": "19:45", "min_duration": 30},
    "Stephanie": {"location": "Nob Hill", "start": "7:30", "end": "9:30", "min_duration": 45},
    "Joseph": {"location": "Alamo Square", "start": "11:30", "end": "12:45", "min_duration": 15},
    "Kimberly": {"location": "North Beach", "start": "15:45", "end": "19:15", "min_duration": 30}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%H:%M")

def can_meet(start, end, min_duration):
    duration = (parse_time(end) - parse_time(start)).seconds // 60
    return duration >= min_duration

def find_optimal_schedule():
    current_location = "Fisherman's Wharf"
    current_time = parse_time("9:00")
    itinerary = []

    def visit(location, person, start, end, min_duration):
        nonlocal current_time, current_location
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + timedelta(minutes=travel_time)
        if arrival_time < parse_time(start):
            arrival_time = parse_time(start)
        departure_time = arrival_time + timedelta(minutes=min_duration)
        if departure_time <= parse_time(end):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(arrival_time),
                "end_time": format_time(departure_time)
            })
            current_time = departure_time
            current_location = location

    # Prioritize meetings based on constraints
    visit(constraints["William"]["location"], "William", "7:00", "9:00", 90)
    visit(constraints["Stephanie"]["location"], "Stephanie", "7:30", "9:30", 45)
    visit(constraints["Joseph"]["location"], "Joseph", "11:30", "12:45", 15)
    visit(constraints["Karen"]["location"], "Karen", "14:30", "19:45", 30)
    visit(constraints["Kimberly"]["location"], "Kimberly", "15:45", "19:15", 30)
    visit(constraints["Laura"]["location"], "Laura", "19:45", "21:30", 105)
    visit(constraints["Daniel"]["location"], "Daniel", "21:15", "21:45", 15)

    return itinerary

itinerary = find_optimal_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))