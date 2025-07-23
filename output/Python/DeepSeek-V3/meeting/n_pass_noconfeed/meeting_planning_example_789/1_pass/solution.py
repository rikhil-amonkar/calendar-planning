import json
from itertools import permutations

# Travel times dictionary
travel_times = {
    "Union Square": {
        "Russian Hill": 13,
        "Alamo Square": 15,
        "Haight-Ashbury": 18,
        "Marina District": 18,
        "Bayview": 15,
        "Chinatown": 7,
        "Presidio": 24,
        "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10,
        "Alamo Square": 15,
        "Haight-Ashbury": 17,
        "Marina District": 7,
        "Bayview": 23,
        "Chinatown": 9,
        "Presidio": 14,
        "Sunset District": 23
    },
    "Alamo Square": {
        "Union Square": 14,
        "Russian Hill": 13,
        "Haight-Ashbury": 5,
        "Marina District": 15,
        "Bayview": 16,
        "Chinatown": 15,
        "Presidio": 17,
        "Sunset District": 16
    },
    "Haight-Ashbury": {
        "Union Square": 19,
        "Russian Hill": 17,
        "Alamo Square": 5,
        "Marina District": 17,
        "Bayview": 18,
        "Chinatown": 19,
        "Presidio": 15,
        "Sunset District": 15
    },
    "Marina District": {
        "Union Square": 16,
        "Russian Hill": 8,
        "Alamo Square": 15,
        "Haight-Ashbury": 16,
        "Bayview": 27,
        "Chinatown": 15,
        "Presidio": 10,
        "Sunset District": 19
    },
    "Bayview": {
        "Union Square": 18,
        "Russian Hill": 23,
        "Alamo Square": 16,
        "Haight-Ashbury": 19,
        "Marina District": 27,
        "Chinatown": 19,
        "Presidio": 32,
        "Sunset District": 23
    },
    "Chinatown": {
        "Union Square": 7,
        "Russian Hill": 7,
        "Alamo Square": 17,
        "Haight-Ashbury": 19,
        "Marina District": 12,
        "Bayview": 20,
        "Presidio": 19,
        "Sunset District": 29
    },
    "Presidio": {
        "Union Square": 22,
        "Russian Hill": 14,
        "Alamo Square": 19,
        "Haight-Ashbury": 15,
        "Marina District": 11,
        "Bayview": 31,
        "Chinatown": 21,
        "Sunset District": 16
    },
    "Sunset District": {
        "Union Square": 30,
        "Russian Hill": 24,
        "Alamo Square": 17,
        "Haight-Ashbury": 15,
        "Marina District": 21,
        "Bayview": 22,
        "Chinatown": 30,
        "Presidio": 16
    }
}

# Friend constraints
friends = [
    {"name": "Betty", "location": "Russian Hill", "available_start": "7:00", "available_end": "16:45", "min_duration": 105},
    {"name": "Melissa", "location": "Alamo Square", "available_start": "9:30", "available_end": "17:15", "min_duration": 105},
    {"name": "Joshua", "location": "Haight-Ashbury", "available_start": "12:15", "available_end": "19:00", "min_duration": 90},
    {"name": "Jeffrey", "location": "Marina District", "available_start": "12:15", "available_end": "18:00", "min_duration": 45},
    {"name": "James", "location": "Bayview", "available_start": "7:30", "available_end": "20:00", "min_duration": 90},
    {"name": "Anthony", "location": "Chinatown", "available_start": "11:45", "available_end": "13:30", "min_duration": 75},
    {"name": "Timothy", "location": "Presidio", "available_start": "12:30", "available_end": "14:45", "min_duration": 90},
    {"name": "Emily", "location": "Sunset District", "available_start": "19:30", "available_end": "21:30", "min_duration": 120}
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_travel_time(from_loc, to_loc):
    return travel_times[from_loc][to_loc]

def is_schedule_valid(schedule):
    current_time = time_to_minutes("9:00")
    current_location = "Union Square"
    
    for meeting in schedule:
        travel_time = get_travel_time(current_location, meeting["location"])
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(meeting["available_start"])
        available_end = time_to_minutes(meeting["available_end"])
        min_duration = meeting["min_duration"]
        
        if arrival_time > available_end:
            return False
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        if end_time > available_end:
            return False
        
        current_time = end_time
        current_location = meeting["location"]
    
    # Check if we can meet Emily in the evening
    travel_time = get_travel_time(current_location, "Sunset District")
    arrival_time = current_time + travel_time
    emily_start = time_to_minutes("19:30")
    emily_end = time_to_minutes("21:30")
    emily_duration = 120
    
    if arrival_time > emily_end:
        return False
    
    emily_start_time = max(arrival_time, emily_start)
    emily_end_time = emily_start_time + emily_duration
    
    if emily_end_time > emily_end:
        return False
    
    return True

def calculate_total_meetings(schedule):
    return len(schedule) + 1  # +1 for Emily

def find_best_schedule():
    non_emily_friends = [f for f in friends if f["name"] != "Emily"]
    best_schedule = None
    max_meetings = 0
    
    # Try all permutations of length 1 to 7
    for r in range(1, len(non_emily_friends) + 1):
        for perm in permutations(non_emily_friends, r):
            if is_schedule_valid(perm):
                num_meetings = calculate_total_meetings(perm)
                if num_meetings > max_meetings:
                    max_meetings = num_meetings
                    best_schedule = perm
    
    return best_schedule

def generate_itinerary(schedule):
    itinerary = []
    current_time = time_to_minutes("9:00")
    current_location = "Union Square"
    
    for meeting in schedule:
        travel_time = get_travel_time(current_location, meeting["location"])
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(meeting["available_start"])
        available_end = time_to_minutes(meeting["available_end"])
        min_duration = meeting["min_duration"]
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        
        current_time = end_time
        current_location = meeting["location"]
    
    # Add Emily meeting
    travel_time = get_travel_time(current_location, "Sunset District")
    arrival_time = current_time + travel_time
    emily_start = time_to_minutes("19:30")
    emily_end = time_to_minutes("21:30")
    emily_duration = 120
    
    emily_start_time = max(arrival_time, emily_start)
    emily_end_time = emily_start_time + emily_duration
    
    itinerary.append({
        "action": "meet",
        "location": "Sunset District",
        "person": "Emily",
        "start_time": minutes_to_time(emily_start_time),
        "end_time": minutes_to_time(emily_end_time)
    })
    
    return itinerary

best_schedule = find_best_schedule()
if best_schedule:
    itinerary = generate_itinerary(best_schedule)
    result = {"itinerary": itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))