import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%H:%M")

def time_add_minutes(time_str, minutes):
    dt = parse_time(time_str)
    dt += timedelta(minutes=minutes)
    return format_time(dt)

def time_diff_minutes(start_str, end_str):
    start = parse_time(start_str)
    end = parse_time(end_str)
    return int((end - start).total_seconds() / 60)

def get_travel_time(from_loc, to_loc):
    travel_times = {
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Sunset District"): 27,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Sunset District"): 23,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Sunset District"): 16,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Sunset District"): 19,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Sunset District"): 23,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Sunset District"): 29,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Sunset District"): 15,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Presidio"): 16
    }
    return travel_times.get((from_loc, to_loc), float('inf'))

friends = [
    {"name": "Betty", "location": "Russian Hill", "available_start": "7:00", "available_end": "16:45", "duration": 105},
    {"name": "Melissa", "location": "Alamo Square", "available_start": "9:30", "available_end": "17:15", "duration": 105},
    {"name": "Joshua", "location": "Haight-Ashbury", "available_start": "12:15", "available_end": "19:00", "duration": 90},
    {"name": "Jeffrey", "location": "Marina District", "available_start": "12:15", "available_end": "18:00", "duration": 45},
    {"name": "James", "location": "Bayview", "available_start": "7:30", "available_end": "20:00", "duration": 90},
    {"name": "Anthony", "location": "Chinatown", "available_start": "11:45", "available_end": "13:30", "duration": 75},
    {"name": "Timothy", "location": "Presidio", "available_start": "12:30", "available_end": "14:45", "duration": 90},
    {"name": "Emily", "location": "Sunset District", "available_start": "19:30", "available_end": "21:30", "duration": 120}
]

def generate_itinerary():
    itinerary = []
    current_time = "9:00"
    current_location = "Union Square"
    
    # Create a copy of friends list to modify
    remaining_friends = friends.copy()
    
    while remaining_friends:
        best_friend = None
        best_start_time = None
        best_end_time = None
        min_wait_time = float('inf')
        
        for friend in remaining_friends:
            # Calculate travel time
            travel_time = get_travel_time(current_location, friend["location"])
            
            # Calculate arrival time
            arrival_time = time_add_minutes(current_time, travel_time)
            
            # Determine when we can start meeting
            meeting_start = max(arrival_time, friend["available_start"])
            
            # Calculate meeting end time
            meeting_end = time_add_minutes(meeting_start, friend["duration"])
            
            # Check if meeting fits in friend's availability
            if (meeting_start >= friend["available_start"] and 
                meeting_end <= friend["available_end"]):
                
                # Calculate wait time (time between current_time and meeting_start)
                wait_time = time_diff_minutes(current_time, meeting_start)
                
                # Prefer friends with minimal wait time
                if wait_time < min_wait_time:
                    best_friend = friend
                    best_start_time = meeting_start
                    best_end_time = meeting_end
                    min_wait_time = wait_time
        
        if best_friend:
            itinerary.append({
                "action": "meet",
                "location": best_friend["location"],
                "person": best_friend["name"],
                "start_time": best_start_time,
                "end_time": best_end_time
            })
            
            # Update current time and location
            current_time = best_end_time
            current_location = best_friend["location"]
            
            # Remove scheduled friend from remaining list
            remaining_friends.remove(best_friend)
        else:
            # No more feasible meetings
            break
    
    return {"itinerary": itinerary}

result = generate_itinerary()
print(json.dumps(result, indent=2))