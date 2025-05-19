import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
locations = {
    "Union Square": 0,
    "Golden Gate Park": 1,
    "Pacific Heights": 2,
    "Presidio": 3,
    "Chinatown": 4,
    "The Castro": 5
}

travel_times = [
    [0, 22, 15, 24, 7, 19],  # Union Square
    [22, 0, 16, 11, 23, 13],  # Golden Gate Park
    [15, 16, 0, 11, 11, 16],  # Pacific Heights
    [24, 11, 11, 0, 21, 21],  # Presidio
    [7, 23, 10, 19, 0, 22],    # Chinatown
    [19, 13, 16, 20, 20, 0]    # The Castro
]

friends = [
    {"name": "Andrew", "location": "Golden Gate Park", "start": "11:45", "end": "14:30", "duration": 75},
    {"name": "Sarah", "location": "Pacific Heights", "start": "16:15", "end": "18:45", "duration": 15},
    {"name": "Nancy", "location": "Presidio", "start": "17:30", "end": "19:15", "duration": 60},
    {"name": "Rebecca", "location": "Chinatown", "start": "9:45", "end": "21:30", "duration": 90},
    {"name": "Robert", "location": "The Castro", "start": "8:30", "end": "14:15", "duration": 30}
]

current_time = time_to_minutes("9:00")
current_location = "Union Square"

def find_best_schedule():
    best_schedule = []
    max_meetings = 0
    
    # Try all permutations of friends to find the best order
    for order in permutations(friends):
        schedule = []
        current_loc = current_location
        current_time_temp = current_time
        meetings = 0
        
        for friend in order:
            loc = friend["location"]
            travel_time = travel_times[locations[current_loc]][locations[loc]]
            arrival_time = current_time_temp + travel_time
            
            start_window = time_to_minutes(friend["start"])
            end_window = time_to_minutes(friend["end"])
            duration = friend["duration"]
            
            # Calculate possible meeting start time
            meeting_start = max(arrival_time, start_window)
            meeting_end = meeting_start + duration
            
            if meeting_end <= end_window:
                schedule.append({
                    "action": "meet",
                    "location": loc,
                    "person": friend["name"],
                    "start_time": minutes_to_time(meeting_start),
                    "end_time": minutes_to_time(meeting_end)
                })
                current_time_temp = meeting_end
                current_loc = loc
                meetings += 1
        
        if meetings > max_meetings:
            max_meetings = meetings
            best_schedule = schedule
        elif meetings == max_meetings and meetings > 0:
            # Prefer schedules that end earlier
            if time_to_minutes(schedule[-1]["end_time"]) < time_to_minutes(best_schedule[-1]["end_time"]):
                best_schedule = schedule
    
    return best_schedule

best_schedule = find_best_schedule()

# Output the result as JSON
output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))