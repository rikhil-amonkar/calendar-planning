import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Fisherman's Wharf": {
        "The Castro": 26, "Golden Gate Park": 25, "Embarcadero": 8, "Russian Hill": 7, "Nob Hill": 11,
        "Alamo Square": 20, "North Beach": 6
    },
    "The Castro": {
        "Fisherman's Wharf": 24, "Golden Gate Park": 11, "Embarcadero": 22, "Russian Hill": 18, "Nob Hill": 16,
        "Alamo Square": 8, "North Beach": 20
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24, "The Castro": 13, "Embarcadero": 25, "Russian Hill": 19, "Nob Hill": 20,
        "Alamo Square": 10, "North Beach": 24
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6, "The Castro": 25, "Golden Gate Park": 25, "Russian Hill": 8, "Nob Hill": 10,
        "Alamo Square": 19, "North Beach": 5
    },
    "Russian Hill": {
        "Fisherman's Wharf": 7, "The Castro": 21, "Golden Gate Park": 21, "Embarcadero": 8, "Nob Hill": 5,
        "Alamo Square": 15, "North Beach": 5
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11, "The Castro": 17, "Golden Gate Park": 17, "Embarcadero": 9, "Russian Hill": 5,
        "Alamo Square": 11, "North Beach": 8
    },
    "Alamo Square": {
        "Fisherman's Wharf": 19, "The Castro": 8, "Golden Gate Park": 9, "Embarcadero": 17, "Russian Hill": 13,
        "Nob Hill": 11, "North Beach": 15
    },
    "North Beach": {
        "Fisherman's Wharf": 5, "The Castro": 22, "Golden Gate Park": 22, "Embarcadero": 6, "Russian Hill": 4,
        "Nob Hill": 7, "Alamo Square": 16
    }
}

# Define constraints
constraints = {
    "Laura": {"location": "The Castro", "start": "19:45", "end": "21:30", "min_duration": 105},
    "Daniel": {"location": "Golden Gate Park", "start": "21:15", "end": "21:45", "min_duration": 15},
    "William": {"location": "Embarcadero", "start": "07:00", "end": "09:00", "min_duration": 90},
    "Karen": {"location": "Russian Hill", "start": "14:30", "end": "19:45", "min_duration": 30},
    "Stephanie": {"location": "Nob Hill", "start": "07:30", "end": "09:30", "min_duration": 45},
    "Joseph": {"location": "Alamo Square", "start": "11:30", "end": "12:45", "min_duration": 15},
    "Kimberly": {"location": "North Beach", "start": "15:45", "end": "19:15", "min_duration": 30}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def add_minutes_to_time(time, minutes):
    return time + timedelta(minutes=minutes)

def time_to_str(time):
    return time.strftime("%H:%M")

def can_meet(constraint, current_time):
    start = parse_time(constraint["start"])
    end = parse_time(constraint["end"])
    min_duration = constraint["min_duration"]
    available_time = end - current_time
    return current_time <= start and available_time.total_seconds() / 60 >= min_duration

def find_next_location(current_location, current_time, remaining_constraints):
    best_location = None
    best_end_time = None
    for person, constraint in remaining_constraints.items():
        location = constraint["location"]
        if can_meet(constraint, current_time):
            travel_time = travel_times[current_location][location]
            start_time = max(parse_time(constraint["start"]), add_minutes_to_time(current_time, travel_time))
            end_time = add_minutes_to_time(start_time, constraint["min_duration"])
            if best_end_time is None or end_time < best_end_time:
                best_location = location
                best_end_time = end_time
    return best_location, best_end_time

def generate_schedule():
    current_time = parse_time("09:00")
    current_location = "Fisherman's Wharf"
    remaining_constraints = constraints.copy()
    itinerary = []

    while remaining_constraints:
        next_location, end_time = find_next_location(current_location, current_time, remaining_constraints)
        if next_location is None:
            break
        travel_time = travel_times[current_location][next_location]
        start_time = add_minutes_to_time(current_time, travel_time)
        person = [k for k, v in remaining_constraints.items() if v["location"] == next_location][0]
        itinerary.append({
            "action": "meet",
            "location": next_location,
            "person": person,
            "start_time": time_to_str(start_time),
            "end_time": time_to_str(end_time)
        })
        del remaining_constraints[person]
        current_time = end_time
        current_location = next_location

    return {"itinerary": itinerary}

# Generate and print the schedule
schedule = generate_schedule()
print(json.dumps(schedule, indent=2))