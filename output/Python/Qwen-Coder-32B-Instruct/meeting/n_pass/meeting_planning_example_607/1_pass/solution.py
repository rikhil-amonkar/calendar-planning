import json
from datetime import datetime, timedelta

# Define the travel times
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

# Define the meeting constraints
constraints = {
    "Karen": {"location": "Russian Hill", "start": "20:45", "end": "21:45", "duration": 60},
    "Jessica": {"location": "The Castro", "start": "15:45", "end": "19:30", "duration": 60},
    "Matthew": {"location": "Richmond District", "start": "07:30", "end": "15:15", "duration": 15},
    "Michelle": {"location": "Marina District", "start": "10:30", "end": "18:45", "duration": 75},
    "Carol": {"location": "North Beach", "start": "12:00", "end": "17:00", "duration": 90},
    "Stephanie": {"location": "Union Square", "start": "10:45", "end": "14:15", "duration": 30},
    "Linda": {"location": "Golden Gate Park", "start": "10:45", "end": "22:00", "duration": 90},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def can_meet(start, end, duration):
    start_time = parse_time(start)
    end_time = parse_time(end)
    return (end_time - start_time).total_seconds() / 60 >= duration

def find_best_schedule(constraints, travel_times):
    current_location = "Sunset District"
    current_time = parse_time("09:00")
    itinerary = []

    def add_to_itinerary(person, location, start, end):
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": start,
            "end_time": end
        })

    def get_travel_time(from_loc, to_loc):
        return travel_times.get((from_loc, to_loc), float('inf'))

    def get_available_slots(location, constraints):
        slots = []
        for person, details in constraints.items():
            if details["location"] == location:
                slots.append((details["start"], details["end"], details["duration"]))
        return slots

    def find_next_meeting(current_location, current_time, constraints):
        best_meeting = None
        best_end_time = float('inf')
        for person, details in constraints.items():
            if can_meet(details["start"], details["end"], details["duration"]):
                travel_time = get_travel_time(current_location, details["location"])
                meeting_start = max(current_time + timedelta(minutes=travel_time), parse_time(details["start"]))
                meeting_end = meeting_start + timedelta(minutes=details["duration"])
                if meeting_end <= parse_time(details["end"]) and meeting_end < best_end_time:
                    best_meeting = (person, details["location"], meeting_start, meeting_end)
                    best_end_time = meeting_end
        return best_meeting

    while current_time < parse_time("21:45"):
        next_meeting = find_next_meeting(current_location, current_time, constraints)
        if next_meeting:
            person, location, start, end = next_meeting
            travel_time = get_travel_time(current_location, location)
            travel_start = current_time
            travel_end = travel_start + timedelta(minutes=travel_time)
            if travel_end <= start:
                add_to_itinerary(None, current_location, travel_start.strftime("%H:%M"), travel_end.strftime("%H:%M"))
                current_time = travel_end
            else:
                current_time = start
            add_to_itinerary(person, location, start.strftime("%H:%M"), end.strftime("%H:%M"))
            current_time = end
            current_location = location
            del constraints[person]
        else:
            break

    return itinerary

itinerary = find_best_schedule(constraints, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result))