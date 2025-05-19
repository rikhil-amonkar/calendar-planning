import json
from itertools import permutations

# Locations
locations = [
    "Presidio",
    "Richmond District",
    "North Beach",
    "Financial District",
    "Golden Gate Park",
    "Union Square"
]

# Travel times in minutes (from_location, to_location) -> minutes
travel_times = {
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Union Square"): 22,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Union Square"): 21,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Union Square"): 7,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Union Square"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Golden Gate Park"): 22
}

# People and their constraints
people = {
    "Jason": {
        "location": "Richmond District",
        "available_start": "13:00",
        "available_end": "20:45",
        "min_duration": 90
    },
    "Melissa": {
        "location": "North Beach",
        "available_start": "18:45",
        "available_end": "20:15",
        "min_duration": 45
    },
    "Brian": {
        "location": "Financial District",
        "available_start": "9:45",
        "available_end": "21:45",
        "min_duration": 15
    },
    "Elizabeth": {
        "location": "Golden Gate Park",
        "available_start": "8:45",
        "available_end": "21:30",
        "min_duration": 105
    },
    "Laura": {
        "location": "Union Square",
        "available_start": "14:15",
        "available_end": "19:30",
        "min_duration": 75
    }
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_travel_time(from_loc, to_loc):
    return travel_times.get((from_loc, to_loc), float('inf'))

def can_schedule(person, start_time, end_time):
    available_start = time_to_minutes(people[person]["available_start"])
    available_end = time_to_minutes(people[person]["available_end"])
    min_duration = people[person]["min_duration"]
    
    actual_start = max(start_time, available_start)
    actual_end = min(end_time, available_end)
    
    if actual_end <= actual_start:
        return False
    
    duration = actual_end - actual_start
    return duration >= min_duration

def generate_schedule(order):
    current_time = time_to_minutes("9:00")  # Start at Presidio at 9:00
    current_location = "Presidio"
    schedule = []
    
    for person in order:
        loc = people[person]["location"]
        travel_time = get_travel_time(current_location, loc)
        if travel_time == float('inf'):
            return None
        
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(people[person]["available_start"])
        available_end = time_to_minutes(people[person]["available_end"])
        min_duration = people[person]["min_duration"]
        
        # Calculate meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = min(meeting_start + min_duration, available_end)
        
        if meeting_end > available_end or (meeting_end - meeting_start) < min_duration:
            return None
        
        schedule.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = loc
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return 0
    return len(schedule)

def find_optimal_schedule():
    best_schedule = None
    best_score = 0
    people_names = list(people.keys())
    
    # Try all permutations of people (limited to 5 for performance)
    for order in permutations(people_names):
        schedule = generate_schedule(order)
        score = evaluate_schedule(schedule)
        if score > best_score:
            best_score = score
            best_schedule = schedule
            if best_score == len(people_names):
                break  # Found optimal
    
    return best_schedule

optimal_schedule = find_optimal_schedule()

result = {
    "itinerary": optimal_schedule if optimal_schedule else []
}

print(json.dumps(result, indent=2))