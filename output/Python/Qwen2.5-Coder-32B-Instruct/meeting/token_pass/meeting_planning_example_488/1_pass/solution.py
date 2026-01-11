import json
from datetime import datetime, timedelta

# Travel times between locations
travel_times = {
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Sunset District"): 25,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Sunset District"): 15,
}

# Meeting constraints
constraints = {
    "Ronald": {"location": "Nob Hill", "start": "10:00", "end": "17:00", "min_duration": 105},
    "Sarah": {"location": "Russian Hill", "start": "07:15", "end": "09:30", "min_duration": 45},
    "Helen": {"location": "The Castro", "start": "13:30", "end": "17:00", "min_duration": 120},
    "Joshua": {"location": "Sunset District", "start": "14:15", "end": "19:30", "min_duration": 90},
    "Margaret": {"location": "Haight-Ashbury", "start": "10:15", "end": "22:00", "min_duration": 60},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_schedule(current_location, current_time, visited, itinerary):
    best_itinerary = itinerary.copy()
    for person, details in constraints.items():
        if person in visited:
            continue
        location = details["location"]
        start = parse_time(details["start"])
        end = parse_time(details["end"])
        min_duration = details["min_duration"]

        # Calculate travel time to the next location
        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Check if we can meet within the available time slot
        if arrival_time >= start and can_meet(arrival_time, end, min_duration):
            meeting_start = max(arrival_time, start)
            meeting_end = meeting_start + timedelta(minutes=min_duration)
            new_itinerary = itinerary + [{
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start.strftime("%H:%M"),
                "end_time": meeting_end.strftime("%H:%M")
            }]
            visited.add(person)
            candidate_itinerary = find_schedule(location, meeting_end, visited, new_itinerary)
            if len(candidate_itinerary) > len(best_itinerary):
                best_itinerary = candidate_itinerary
            visited.remove(person)
    return best_itinerary

# Start from Pacific Heights at 9:00 AM
initial_time = parse_time("09:00")
initial_location = "Pacific Heights"
visited = set()
best_itinerary = find_schedule(initial_location, initial_time, visited, [])

# Output the result as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))