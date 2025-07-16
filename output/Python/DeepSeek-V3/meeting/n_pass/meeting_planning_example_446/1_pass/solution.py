import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
initial_location = "Richmond District"
initial_time = "9:00"

friends = [
    {"name": "Kimberly", "location": "Marina District", "start": "13:15", "end": "16:45", "duration": 15},
    {"name": "Robert", "location": "Chinatown", "start": "12:15", "end": "20:15", "duration": 15},
    {"name": "Rebecca", "location": "Financial District", "start": "13:15", "end": "16:45", "duration": 75},
    {"name": "Margaret", "location": "Bayview", "start": "9:30", "end": "13:30", "duration": 30},
    {"name": "Kenneth", "location": "Union Square", "start": "19:30", "end": "21:15", "duration": 75}
]

travel_times = {
    "Richmond District": {
        "Marina District": 9,
        "Chinatown": 20,
        "Financial District": 22,
        "Bayview": 26,
        "Union Square": 21
    },
    "Marina District": {
        "Richmond District": 11,
        "Chinatown": 16,
        "Financial District": 17,
        "Bayview": 27,
        "Union Square": 16
    },
    "Chinatown": {
        "Richmond District": 20,
        "Marina District": 12,
        "Financial District": 5,
        "Bayview": 22,
        "Union Square": 7
    },
    "Financial District": {
        "Richmond District": 21,
        "Marina District": 15,
        "Chinatown": 5,
        "Bayview": 19,
        "Union Square": 9
    },
    "Bayview": {
        "Richmond District": 25,
        "Marina District": 25,
        "Chinatown": 18,
        "Financial District": 19,
        "Union Square": 17
    },
    "Union Square": {
        "Richmond District": 20,
        "Marina District": 18,
        "Chinatown": 7,
        "Financial District": 9,
        "Bayview": 15
    }
}

def get_travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
    try:
        return travel_times[from_loc][to_loc]
    except KeyError:
        return travel_times[to_loc][from_loc]

def generate_schedules():
    best_schedule = None
    max_meetings = 0
    
    for perm in permutations(friends):
        current_time = time_to_minutes(initial_time)
        current_location = initial_location
        schedule = []
        valid = True
        
        for friend in perm:
            travel_time = get_travel_time(current_location, friend["location"])
            arrival_time = current_time + travel_time
            start_window = time_to_minutes(friend["start"])
            end_window = time_to_minutes(friend["end"])
            
            if arrival_time > end_window:
                valid = False
                break
                
            start_meeting = max(arrival_time, start_window)
            end_meeting = start_meeting + friend["duration"]
            
            if end_meeting > end_window:
                valid = False
                break
                
            schedule.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(start_meeting),
                "end_time": minutes_to_time(end_meeting)
            })
            
            current_time = end_meeting
            current_location = friend["location"]
        
        if valid and len(schedule) > max_meetings:
            max_meetings = len(schedule)
            best_schedule = schedule
    
    return best_schedule

def main():
    best_schedule = generate_schedules()
    
    if best_schedule is None:
        print(json.dumps({"itinerary": []}))
    else:
        print(json.dumps({"itinerary": best_schedule}, indent=2))

if __name__ == "__main__":
    main()