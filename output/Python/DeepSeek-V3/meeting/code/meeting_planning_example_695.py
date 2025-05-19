import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
friends = [
    {"name": "Paul", "location": "Nob Hill", "available_start": "16:15", "available_end": "21:15", "min_duration": 60},
    {"name": "Carol", "location": "Union Square", "available_start": "18:00", "available_end": "20:15", "min_duration": 120},
    {"name": "Patricia", "location": "Chinatown", "available_start": "20:00", "available_end": "21:30", "min_duration": 75},
    {"name": "Karen", "location": "The Castro", "available_start": "17:00", "available_end": "19:00", "min_duration": 45},
    {"name": "Nancy", "location": "Presidio", "available_start": "11:45", "available_end": "22:00", "min_duration": 30},
    {"name": "Jeffrey", "location": "Pacific Heights", "available_start": "20:00", "available_end": "20:45", "min_duration": 45},
    {"name": "Matthew", "location": "Russian Hill", "available_start": "15:45", "available_end": "21:45", "min_duration": 75}
]

travel_times = {
    "Bayview": {
        "Nob Hill": 20, "Union Square": 17, "Chinatown": 18, "The Castro": 20,
        "Presidio": 31, "Pacific Heights": 23, "Russian Hill": 23
    },
    "Nob Hill": {
        "Bayview": 19, "Union Square": 7, "Chinatown": 6, "The Castro": 17,
        "Presidio": 17, "Pacific Heights": 8, "Russian Hill": 5
    },
    "Union Square": {
        "Bayview": 15, "Nob Hill": 9, "Chinatown": 7, "The Castro": 19,
        "Presidio": 24, "Pacific Heights": 15, "Russian Hill": 13
    },
    "Chinatown": {
        "Bayview": 22, "Nob Hill": 8, "Union Square": 7, "The Castro": 22,
        "Presidio": 19, "Pacific Heights": 10, "Russian Hill": 7
    },
    "The Castro": {
        "Bayview": 19, "Nob Hill": 16, "Union Square": 19, "Chinatown": 20,
        "Presidio": 20, "Pacific Heights": 16, "Russian Hill": 18
    },
    "Presidio": {
        "Bayview": 31, "Nob Hill": 18, "Union Square": 22, "Chinatown": 21,
        "The Castro": 21, "Pacific Heights": 11, "Russian Hill": 14
    },
    "Pacific Heights": {
        "Bayview": 22, "Nob Hill": 8, "Union Square": 12, "Chinatown": 11,
        "The Castro": 16, "Presidio": 11, "Russian Hill": 7
    },
    "Russian Hill": {
        "Bayview": 23, "Nob Hill": 5, "Union Square": 11, "Chinatown": 9,
        "The Castro": 21, "Presidio": 14, "Pacific Heights": 7
    }
}

def evaluate_schedule(order):
    current_time = time_to_minutes("9:00")
    current_location = "Bayview"
    itinerary = []
    total_meetings = 0
    
    for friend in order:
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]
        
        # Calculate meeting start and end times
        meeting_start = max(arrival_time, available_start)
        meeting_end = min(meeting_start + min_duration, available_end)
        
        if meeting_end <= available_end and meeting_end - meeting_start >= min_duration:
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = friend["location"]
            total_meetings += 1
        else:
            return None, 0
    
    return itinerary, total_meetings

def find_optimal_schedule():
    best_schedule = None
    max_meetings = 0
    
    # Try all permutations of 5 friends (since meeting all 7 is impossible due to time constraints)
    for perm in permutations(friends, 5):
        itinerary, total_meetings = evaluate_schedule(perm)
        if total_meetings > max_meetings:
            max_meetings = total_meetings
            best_schedule = itinerary
    
    # If no 5-meeting schedule found, try 4
    if max_meetings < 5:
        for perm in permutations(friends, 4):
            itinerary, total_meetings = evaluate_schedule(perm)
            if total_meetings > max_meetings:
                max_meetings = total_meetings
                best_schedule = itinerary
    
    # If no 4-meeting schedule found, try 3
    if max_meetings < 4:
        for perm in permutations(friends, 3):
            itinerary, total_meetings = evaluate_schedule(perm)
            if total_meetings > max_meetings:
                max_meetings = total_meetings
                best_schedule = itinerary
    
    return best_schedule

optimal_schedule = find_optimal_schedule()
result = {"itinerary": optimal_schedule} if optimal_schedule else {"itinerary": []}
print(json.dumps(result, indent=2))