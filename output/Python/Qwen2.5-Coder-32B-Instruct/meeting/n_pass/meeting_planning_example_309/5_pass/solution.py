import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "Bayview"): 26
}

# Define meeting constraints
constraints = {
    "Nancy": {"location": "Chinatown", "start": "9:30", "end": "13:30", "min_duration": 90},
    "Mary": {"location": "Alamo Square", "start": "7:00", "end": "21:00", "min_duration": 75},
    "Jessica": {"location": "Bayview", "start": "11:15", "end": "13:45", "min_duration": 45},
    "Rebecca": {"location": "Fisherman's Wharf", "start": "7:00", "end": "8:30", "min_duration": 45}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M").time()

def format_time(dt):
    return dt.strftime("%H:%M")

def find_optimal_schedule(constraints, travel_times):
    start_time = datetime.strptime("9:00", "%H:%M")
    current_location = "Financial District"
    itinerary = []

    def can_meet(person, current_time):
        constraint = constraints[person]
        person_start = datetime.strptime(constraint["start"], "%H:%M")
        person_end = datetime.strptime(constraint["end"], "%H:%M")
        min_duration = constraint["min_duration"]
        return person_start <= current_time <= person_end - timedelta(minutes=min_duration)

    def add_meeting(person, start_time):
        constraint = constraints[person]
        end_time = start_time + timedelta(minutes=constraint["min_duration"])
        itinerary.append({
            "action": "meet",
            "location": constraint["location"],
            "person": person,
            "start_time": format_time(start_time),
            "end_time": format_time(end_time)
        })
        return end_time

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: datetime.strptime(x[1]["start"], "%H:%M"))

    for person, constraint in sorted_constraints:
        person_start = datetime.strptime(constraint["start"], "%H:%M")
        person_end = datetime.strptime(constraint["end"], "%H:%M")
        min_duration = constraint["min_duration"]
        meeting_location = constraint["location"]

        # Calculate travel time to the next meeting location
        travel_time = travel_times[(current_location, meeting_location)]

        # Check if we can reach the meeting location on time
        potential_start_time = start_time + timedelta(minutes=travel_time)
        
        if can_meet(person, potential_start_time):
            start_time = add_meeting(person, potential_start_time)
            current_location = meeting_location
        elif can_meet(person, person_start):
            start_time = add_meeting(person, person_start)
            current_location = meeting_location
        else:
            # If we cannot meet the person at their preferred time, skip them
            continue

    return itinerary

itinerary = find_optimal_schedule(constraints, travel_times)
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))