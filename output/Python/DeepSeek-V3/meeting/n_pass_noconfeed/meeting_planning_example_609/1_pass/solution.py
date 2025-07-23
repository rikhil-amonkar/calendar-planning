import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    "Chinatown": {
        "Mission District": 18,
        "Alamo Square": 17,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Golden Gate Park": 23,
        "Sunset District": 29,
        "Presidio": 19
    },
    "Mission District": {
        "Chinatown": 16,
        "Alamo Square": 11,
        "Pacific Heights": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Sunset District": 24,
        "Presidio": 25
    },
    "Alamo Square": {
        "Chinatown": 16,
        "Mission District": 10,
        "Pacific Heights": 10,
        "Union Square": 14,
        "Golden Gate Park": 9,
        "Sunset District": 16,
        "Presidio": 18
    },
    "Pacific Heights": {
        "Chinatown": 11,
        "Mission District": 15,
        "Alamo Square": 10,
        "Union Square": 12,
        "Golden Gate Park": 15,
        "Sunset District": 21,
        "Presidio": 11
    },
    "Union Square": {
        "Chinatown": 7,
        "Mission District": 14,
        "Alamo Square": 15,
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "Sunset District": 26,
        "Presidio": 24
    },
    "Golden Gate Park": {
        "Chinatown": 23,
        "Mission District": 17,
        "Alamo Square": 10,
        "Pacific Heights": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Presidio": 11
    },
    "Sunset District": {
        "Chinatown": 30,
        "Mission District": 24,
        "Alamo Square": 17,
        "Pacific Heights": 21,
        "Union Square": 30,
        "Golden Gate Park": 11,
        "Presidio": 16
    },
    "Presidio": {
        "Chinatown": 21,
        "Mission District": 26,
        "Alamo Square": 18,
        "Pacific Heights": 11,
        "Union Square": 22,
        "Golden Gate Park": 12,
        "Sunset District": 15
    }
}

# Friend constraints
friends = {
    "David": {
        "location": "Mission District",
        "available_start": "8:00",
        "available_end": "19:45",
        "min_duration": 45
    },
    "Kenneth": {
        "location": "Alamo Square",
        "available_start": "14:00",
        "available_end": "19:45",
        "min_duration": 120
    },
    "John": {
        "location": "Pacific Heights",
        "available_start": "17:00",
        "available_end": "20:00",
        "min_duration": 15
    },
    "Charles": {
        "location": "Union Square",
        "available_start": "21:45",
        "available_end": "22:45",
        "min_duration": 60
    },
    "Deborah": {
        "location": "Golden Gate Park",
        "available_start": "7:00",
        "available_end": "18:15",
        "min_duration": 90
    },
    "Karen": {
        "location": "Sunset District",
        "available_start": "17:45",
        "available_end": "21:15",
        "min_duration": 15
    },
    "Carol": {
        "location": "Presidio",
        "available_start": "8:15",
        "available_end": "9:15",
        "min_duration": 30
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
    return travel_times[from_loc][to_loc]

def is_meeting_possible(schedule, friend_name, start_time, end_time):
    friend = friends[friend_name]
    available_start = time_to_minutes(friend["available_start"])
    available_end = time_to_minutes(friend["available_end"])
    min_duration = friend["min_duration"]
    
    if start_time < available_start or end_time > available_end:
        return False
    
    if (end_time - start_time) < min_duration:
        return False
    
    for meeting in schedule:
        if (start_time < meeting["end_time"] and end_time > meeting["start_time"]):
            return False
    
    return True

def generate_schedule(order):
    current_location = "Chinatown"
    current_time = time_to_minutes("9:00")
    schedule = []
    
    for friend_name in order:
        friend = friends[friend_name]
        location = friend["location"]
        travel_time = get_travel_time(current_location, location)
        arrival_time = current_time + travel_time
        
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]
        
        # Try to schedule as early as possible
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        if not is_meeting_possible(schedule, friend_name, start_time, end_time):
            # Try to schedule at the end of availability
            end_time = available_end
            start_time = end_time - min_duration
            if not is_meeting_possible(schedule, friend_name, start_time, end_time):
                return None
        
        schedule.append({
            "action": "meet",
            "location": location,
            "person": friend_name,
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        
        current_location = location
        current_time = end_time
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return -1
    return len(schedule)

def find_best_schedule():
    best_schedule = None
    best_score = -1
    friend_names = list(friends.keys())
    
    # Try all possible orders (permutations) of friends
    for order in permutations(friend_names):
        schedule = generate_schedule(order)
        score = evaluate_schedule(schedule)
        if score > best_score:
            best_score = score
            best_schedule = schedule
            if best_score == len(friend_names):
                break  # Found optimal solution
    
    return best_schedule

best_schedule = find_best_schedule()

result = {
    "itinerary": best_schedule if best_schedule else []
}

print(json.dumps(result, indent=2))