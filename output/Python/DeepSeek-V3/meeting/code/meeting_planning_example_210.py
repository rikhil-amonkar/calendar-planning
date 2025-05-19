import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def add_minutes(time_str, minutes):
    dt = parse_time(time_str)
    dt += timedelta(minutes=minutes)
    return format_time(dt)

def compute_schedule():
    # Input parameters
    start_location = "Fisherman's Wharf"
    start_time = "9:00"
    
    # Friend constraints
    friends = [
        {
            "name": "Emily",
            "location": "Presidio",
            "available_start": "16:15",
            "available_end": "21:00",
            "min_duration": 105,
            "travel_times": {
                "Fisherman's Wharf": 17,
                "Presidio": 0,
                "Richmond District": 7,
                "Financial District": 23
            }
        },
        {
            "name": "Joseph",
            "location": "Richmond District",
            "available_start": "17:15",
            "available_end": "22:00",
            "min_duration": 120,
            "travel_times": {
                "Fisherman's Wharf": 18,
                "Presidio": 7,
                "Richmond District": 0,
                "Financial District": 22
            }
        },
        {
            "name": "Melissa",
            "location": "Financial District",
            "available_start": "15:45",
            "available_end": "21:45",
            "min_duration": 75,
            "travel_times": {
                "Fisherman's Wharf": 11,
                "Presidio": 23,
                "Richmond District": 22,
                "Financial District": 0
            }
        }
    ]
    
    # Travel times lookup
    travel_times = {
        "Fisherman's Wharf": {
            "Presidio": 17,
            "Richmond District": 18,
            "Financial District": 11
        },
        "Presidio": {
            "Fisherman's Wharf": 19,
            "Richmond District": 7,
            "Financial District": 23
        },
        "Richmond District": {
            "Fisherman's Wharf": 18,
            "Presidio": 7,
            "Financial District": 22
        },
        "Financial District": {
            "Fisherman's Wharf": 10,
            "Presidio": 22,
            "Richmond District": 21
        }
    }
    
    # Generate all possible meeting orders
    from itertools import permutations
    best_schedule = None
    max_meetings = 0
    
    for order in permutations(friends):
        current_location = start_location
        current_time = start_time
        schedule = []
        meetings = 0
        
        for friend in order:
            # Calculate travel time to friend's location
            travel_time = travel_times[current_location].get(friend["location"], 0)
            arrival_time = add_minutes(current_time, travel_time)
            
            # Determine meeting window
            meeting_start = max(arrival_time, friend["available_start"])
            meeting_end = add_minutes(meeting_start, friend["min_duration"])
            
            if parse_time(meeting_end) > parse_time(friend["available_end"]):
                continue  # Can't meet this friend
            
            # Add to schedule
            schedule.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": meeting_start,
                "end_time": meeting_end
            })
            meetings += 1
            current_location = friend["location"]
            current_time = meeting_end
        
        if meetings > max_meetings or (meetings == max_meetings and best_schedule is None):
            max_meetings = meetings
            best_schedule = schedule
    
    # If no schedule meets all constraints, try with fewer meetings
    if max_meetings < len(friends):
        for order in permutations(friends, 2):
            current_location = start_location
            current_time = start_time
            schedule = []
            meetings = 0
            
            for friend in order:
                travel_time = travel_times[current_location].get(friend["location"], 0)
                arrival_time = add_minutes(current_time, travel_time)
                
                meeting_start = max(arrival_time, friend["available_start"])
                meeting_end = add_minutes(meeting_start, friend["min_duration"])
                
                if parse_time(meeting_end) > parse_time(friend["available_end"]):
                    break
                
                schedule.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": meeting_start,
                    "end_time": meeting_end
                })
                meetings += 1
                current_location = friend["location"]
                current_time = meeting_end
            
            if meetings > max_meetings:
                max_meetings = meetings
                best_schedule = schedule
    
    return {"itinerary": best_schedule} if best_schedule else {"itinerary": []}

result = compute_schedule()
print(json.dumps(result, indent=2))