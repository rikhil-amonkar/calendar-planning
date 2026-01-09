import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define locations
    locations = [
        "Russian Hill", "Presidio", "Chinatown", "Pacific Heights", 
        "Richmond District", "Fisherman's Wharf", "Golden Gate Park", "Bayview"
    ]
    
    # Travel times matrix (minutes)
    travel_times = {
        "Russian Hill": {"Presidio": 14, "Chinatown": 9, "Pacific Heights": 7, 
                        "Richmond District": 14, "Fisherman's Wharf": 7, 
                        "Golden Gate Park": 21, "Bayview": 23},
        "Presidio": {"Russian Hill": 14, "Chinatown": 21, "Pacific Heights": 11, 
                    "Richmond District": 7, "Fisherman's Wharf": 19, 
                    "Golden Gate Park": 12, "Bayview": 31},
        "Chinatown": {"Russian Hill": 7, "Presidio": 19, "Pacific Heights": 10, 
                     "Richmond District": 20, "Fisherman's Wharf": 8, 
                     "Golden Gate Park": 23, "Bayview": 22},
        "Pacific Heights": {"Russian Hill": 7, "Presidio": 11, "Chinatown": 11, 
                           "Richmond District": 12, "Fisherman's Wharf": 13, 
                           "Golden Gate Park": 15, "Bayview": 22},
        "Richmond District": {"Russian Hill": 13, "Presidio": 7, "Chinatown": 20, 
                             "Pacific Heights": 10, "Fisherman's Wharf": 18, 
                             "Golden Gate Park": 9, "Bayview": 26},
        "Fisherman's Wharf": {"Russian Hill": 7, "Presidio": 17, "Chinatown": 12, 
                             "Pacific Heights": 12, "Richmond District": 18, 
                             "Golden Gate Park": 25, "Bayview": 26},
        "Golden Gate Park": {"Russian Hill": 19, "Presidio": 11, "Chinatown": 23, 
                            "Pacific Heights": 16, "Richmond District": 7, 
                            "Fisherman's Wharf": 24, "Bayview": 23},
        "Bayview": {"Russian Hill": 23, "Presidio": 31, "Chinatown": 18, 
                   "Pacific Heights": 23, "Richmond District": 25, 
                   "Fisherman's Wharf": 25, "Golden Gate Park": 22}
    }
    
    # Friend constraints
    friends = {
        "Matthew": {
            "location": "Presidio",
            "available_start": datetime.strptime("11:00", "%H:%M"),
            "available_end": datetime.strptime("21:00", "%H:%M"),
            "min_duration": 90  # minutes
        },
        "Margaret": {
            "location": "Chinatown",
            "available_start": datetime.strptime("9:15", "%H:%M"),
            "available_end": datetime.strptime("18:45", "%H:%M"),
            "min_duration": 90
        },
        "Nancy": {
            "location": "Pacific Heights",
            "available_start": datetime.strptime("14:15", "%H:%M"),
            "available_end": datetime.strptime("17:00", "%H:%M"),
            "min_duration": 15
        },
        "Helen": {
            "location": "Richmond District",
            "available_start": datetime.strptime("19:45", "%H:%M"),
            "available_end": datetime.strptime("22:00", "%H:%M"),
            "min_duration": 60
        },
        "Rebecca": {
            "location": "Fisherman's Wharf",
            "available_start": datetime.strptime("21:15", "%H:%M"),
            "available_end": datetime.strptime("22:15", "%H:%M"),
            "min_duration": 60
        },
        "Kimberly": {
            "location": "Golden Gate Park",
            "available_start": datetime.strptime("13:00", "%H:%M"),
            "available_end": datetime.strptime("16:30", "%H:%M"),
            "min_duration": 120
        },
        "Kenneth": {
            "location": "Bayview",
            "available_start": datetime.strptime("14:30", "%H:%M"),
            "available_end": datetime.strptime("18:00", "%H:%M"),
            "min_duration": 60
        }
    }
    
    # Start at Russian Hill at 9:00
    start_time = datetime.strptime("9:00", "%H:%M")
    current_location = "Russian Hill"
    current_time = start_time
    
    # We'll try to meet friends in different orders and find the best schedule
    friend_names = list(friends.keys())
    
    best_schedule = None
    max_meetings = 0
    
    # Try different permutations of friend visits
    from itertools import permutations
    import random
    
    # Sample a reasonable number of permutations to avoid combinatorial explosion
    sample_size = min(1000, len(list(permutations(friend_names))))
    permutations_sample = random.sample(list(permutations(friend_names)), sample_size)
    
    for perm in permutations_sample:
        schedule = []
        current_loc = current_location
        current_time_val = current_time
        
        valid_schedule = True
        
        for friend in perm:
            friend_info = friends[friend]
            loc = friend_info["location"]
            available_start = friend_info["available_start"]
            available_end = friend_info["available_end"]
            min_duration = friend_info["min_duration"]
            
            # Calculate travel time
            travel_time = travel_times[current_loc][loc]
            
            # Arrival time at friend's location
            arrival_time = current_time_val + timedelta(minutes=travel_time)
            
            # Check if we arrive before friend's availability ends
            if arrival_time >= available_end:
                valid_schedule = False
                break
            
            # Start meeting at the later of arrival time or friend's available start
            meeting_start = max(arrival_time, available_start)
            
            # Check if we can have the minimum duration
            if meeting_start + timedelta(minutes=min_duration) > available_end:
                valid_schedule = False
                break
            
            # Schedule the meeting for the minimum duration
            meeting_end = meeting_start + timedelta(minutes=min_duration)
            
            # Add to schedule
            schedule.append({
                "action": "meet",
                "location": loc,
                "person": friend,
                "start_time": meeting_start.strftime("%H:%M"),
                "end_time": meeting_end.strftime("%H:%M")
            })
            
            # Update current location and time
            current_loc = loc
            current_time_val = meeting_end
        
        if valid_schedule and len(schedule) > max_meetings:
            max_meetings = len(schedule)
            best_schedule = schedule
    
    # If no valid schedule found with all constraints, try a greedy approach
    if best_schedule is None:
        best_schedule = greedy_schedule(friends, travel_times, current_location, start_time)
    
    # Output the result
    result = {
        "itinerary": best_schedule
    }
    
    print(json.dumps(result, indent=2))

def greedy_schedule(friends, travel_times, start_location, start_time):
    """Fallback greedy scheduling algorithm"""
    schedule = []
    current_location = start_location
    current_time = start_time
    
    # Sort friends by earliest available start time
    sorted_friends = sorted(friends.items(), key=lambda x: x[1]["available_start"])
    
    for friend_name, friend_info in sorted_friends:
        loc = friend_info["location"]
        available_start = friend_info["available_start"]
        available_end = friend_info["available_end"]
        min_duration = friend_info["min_duration"]
        
        # Calculate travel time
        travel_time = travel_times[current_location][loc]
        
        # Arrival time at friend's location
        arrival_time = current_time + timedelta(minutes=travel_time)
        
        # Check if we can meet this friend
        if arrival_time < available_end:
            meeting_start = max(arrival_time, available_start)
            meeting_end = meeting_start + timedelta(minutes=min_duration)
            
            if meeting_end <= available_end:
                schedule.append({
                    "action": "meet",
                    "location": loc,
                    "person": friend_name,
                    "start_time": meeting_start.strftime("%H:%M"),
                    "end_time": meeting_end.strftime("%H:%M")
                })
                
                current_location = loc
                current_time = meeting_end
    
    return schedule

if __name__ == "__main__":
    main()