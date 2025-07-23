import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule():
    # Locations
    locations = [
        "Financial District",
        "Russian Hill",
        "Sunset District",
        "North Beach",
        "The Castro",
        "Golden Gate Park"
    ]
    
    # Travel times in minutes (from_location, to_location): time
    travel_times = {
        ("Financial District", "Russian Hill"): 10,
        ("Financial District", "Sunset District"): 31,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "The Castro"): 23,
        ("Financial District", "Golden Gate Park"): 23,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "North Beach"): 29,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Golden Gate Park"): 11,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "The Castro"): 22,
        ("North Beach", "Golden Gate Park"): 22,
        ("The Castro", "Financial District"): 20,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Golden Gate Park"): 11,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "The Castro"): 13
    }
    
    # Friend constraints
    friends = [
        {
            "name": "Ronald",
            "location": "Russian Hill",
            "available_start": "13:45",
            "available_end": "17:15",
            "min_duration": 105
        },
        {
            "name": "Patricia",
            "location": "Sunset District",
            "available_start": "9:15",
            "available_end": "22:00",
            "min_duration": 60
        },
        {
            "name": "Laura",
            "location": "North Beach",
            "available_start": "12:30",
            "available_end": "12:45",
            "min_duration": 15
        },
        {
            "name": "Emily",
            "location": "The Castro",
            "available_start": "16:15",
            "available_end": "18:30",
            "min_duration": 60
        },
        {
            "name": "Mary",
            "location": "Golden Gate Park",
            "available_start": "15:00",
            "available_end": "16:30",
            "min_duration": 60
        }
    ]
    
    # Initial state
    current_location = "Financial District"
    current_time = time_to_minutes("9:00")
    itinerary = []
    
    # We'll try to meet friends in different orders to find the best schedule
    best_itinerary = None
    max_meetings = 0
    
    for order in permutations(friends):
        temp_itinerary = []
        temp_location = current_location
        temp_time = current_time
        meetings = 0
        
        for friend in order:
            # Check if we can meet this friend
            available_start = time_to_minutes(friend["available_start"])
            available_end = time_to_minutes(friend["available_end"])
            min_duration = friend["min_duration"]
            location = friend["location"]
            
            # Travel time to friend's location
            travel_time = travel_times.get((temp_location, location), float('inf'))
            arrival_time = temp_time + travel_time
            
            # Check if we can arrive before available_end - min_duration
            latest_start = available_end - min_duration
            if arrival_time > latest_start:
                continue  # Can't meet this friend
            
            # Determine start time (max of arrival_time and available_start)
            start_time = max(arrival_time, available_start)
            end_time = start_time + min_duration
            
            if end_time > available_end:
                continue  # Can't meet for required duration
            
            # Add to itinerary
            temp_itinerary.append({
                "action": "meet",
                "location": location,
                "person": friend["name"],
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
            
            meetings += 1
            temp_location = location
            temp_time = end_time
        
        if meetings > max_meetings or (meetings == max_meetings and best_itinerary is None):
            max_meetings = meetings
            best_itinerary = temp_itinerary
    
    return {"itinerary": best_itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))