import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Embarcadero"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Embarcadero"): 9,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Embarcadero"): 19,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Mission District"): 20
}

# Define meeting constraints
constraints = {
    "Patricia": {"location": "Nob Hill", "start": "18:30", "end": "21:45", "min_duration": 90},
    "Ashley": {"location": "Mission District", "start": "20:30", "end": "21:15", "min_duration": 45},
    "Timothy": {"location": "Embarcadero", "start": "9:45", "end": "17:45", "min_duration": 120}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def add_minutes(time_obj, minutes):
    return time_obj + timedelta(minutes=minutes)

def can_meet(start, end, min_duration):
    return (parse_time(end) - parse_time(start)).total_seconds() / 60 >= min_duration

def find_schedule():
    current_time = parse_time("9:00")
    current_location = "Russian Hill"
    itinerary = []

    def visit(location, person, start, end, min_duration):
        nonlocal current_time, current_location, itinerary
        travel_time = travel_times[(current_location, location)]
        arrival_time = add_minutes(current_time, travel_time)
        meeting_start = max(arrival_time, parse_time(start))
        meeting_end = min(add_minutes(meeting_start, min_duration), parse_time(end))
        if can_meet(meeting_start.strftime("%H:%M"), meeting_end.strftime("%H:%M"), min_duration):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start.strftime("%H:%M"),
                "end_time": meeting_end.strftime("%H:%M")
            })
            current_time = meeting_end
            current_location = location

    # Prioritize Timothy since he has the longest meeting window
    visit(constraints["Timothy"]["location"], "Timothy", constraints["Timothy"]["start"], constraints["Timothy"]["end"], constraints["Timothy"]["min_duration"])
    
    # Then try to meet Patricia
    visit(constraints["Patricia"]["location"], "Patricia", constraints["Patricia"]["start"], constraints["Patricia"]["end"], constraints["Patricia"]["min_duration"])
    
    # Finally, try to meet Ashley
    visit(constraints["Ashley"]["location"], "Ashley", constraints["Ashley"]["start"], constraints["Ashley"]["end"], constraints["Ashley"]["min_duration"])

    return itinerary

schedule = find_schedule()
output = {"itinerary": schedule}
print(json.dumps(output))