import json
from itertools import permutations

def time_to_minutes(time_str):
    """Convert time string 'H:MM' to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string 'H:MM'."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
arrival_time = "9:00"
arrival_location = "Embarcadero"

friends = [
    {
        "name": "Stephanie",
        "location": "Financial District",
        "available_start": "8:15",
        "available_end": "11:30",
        "min_duration": 90,
        "travel_from_prev": {
            "Embarcadero": 5,
            "Financial District": 0,
            "Alamo Square": 17
        }
    },
    {
        "name": "John",
        "location": "Alamo Square",
        "available_start": "10:15",
        "available_end": "20:45",
        "min_duration": 30,
        "travel_from_prev": {
            "Embarcadero": 19,
            "Financial District": 17,
            "Alamo Square": 0
        }
    }
]

# Travel times matrix
travel_times = {
    "Embarcadero": {
        "Financial District": 5,
        "Alamo Square": 19
    },
    "Financial District": {
        "Embarcadero": 4,
        "Alamo Square": 17
    },
    "Alamo Square": {
        "Embarcadero": 17,
        "Financial District": 17
    }
}

def calculate_schedule(order):
    current_time = time_to_minutes(arrival_time)
    current_location = arrival_location
    schedule = []
    
    for friend in order:
        # Travel to friend's location
        travel_time = travel_times[current_location][friend["location"]]
        current_time += travel_time
        current_location = friend["location"]
        
        # Determine meeting window
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]
        
        # Calculate meeting start and end
        meeting_start = max(current_time, available_start)
        meeting_end = meeting_start + min_duration
        
        if meeting_end > available_end:
            return None  # This schedule doesn't work
        
        schedule.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
    
    return schedule

# Generate all possible meeting orders
possible_orders = permutations(friends)

best_schedule = None
best_meetings = 0

for order in possible_orders:
    schedule = calculate_schedule(order)
    if schedule and len(schedule) > best_meetings:
        best_schedule = schedule
        best_meetings = len(schedule)

# Output the result
if best_schedule:
    result = {"itinerary": best_schedule}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))