import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes
    travel_times = {
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Fisherman\'s Wharf'): 29,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Fisherman\'s Wharf', 'Sunset District'): 27,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Presidio'): 17
    }
    
    # Friend information
    friends = [
        {
            "name": "Michelle",
            "location": "Chinatown",
            "start_avail": time_to_minutes("8:15"),
            "end_avail": time_to_minutes("14:00"),
            "duration": 15
        },
        {
            "name": "George",
            "location": "Presidio",
            "start_avail": time_to_minutes("10:30"),
            "end_avail": time_to_minutes("18:45"),
            "duration": 30
        },
        {
            "name": "Robert",
            "location": "Fisherman's Wharf",
            "start_avail": time_to_minutes("9:00"),
            "end_avail": time_to_minutes("13:45"),
            "duration": 30
        },
        {
            "name": "William",
            "location": "Russian Hill",
            "start_avail": time_to_minutes("18:30"),
            "end_avail": time_to_minutes("20:45"),
            "duration": 105
        }
    ]
    
    # Start from Sunset District at 9:00
    current_time = time_to_minutes("9:00")
    current_location = "Sunset District"
    itinerary = []
    
    # Try different orders to find the best schedule
    from itertools import permutations
    
    best_itinerary = []
    max_meetings = 0
    
    # Try all possible orders of meeting friends
    for order in permutations(friends):
        temp_itinerary = []
        temp_current_time = current_time
        temp_current_location = current_location
        meetings_count = 0
        
        for friend in order:
            # Calculate travel time
            travel_time = travel_times.get((temp_current_location, friend["location"]), 60)
            
            # Earliest we can start meeting
            earliest_start = max(temp_current_time + travel_time, friend["start_avail"])
            
            # Check if we can complete the meeting within availability
            if earliest_start + friend["duration"] <= friend["end_avail"]:
                # Schedule the meeting
                temp_itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(earliest_start),
                    "end_time": minutes_to_time(earliest_start + friend["duration"])
                })
                meetings_count += 1
                temp_current_time = earliest_start + friend["duration"]
                temp_current_location = friend["location"]
            else:
                # Skip this friend if we can't meet them
                continue
        
        # Update best itinerary if this order results in more meetings
        if meetings_count > max_meetings:
            max_meetings = meetings_count
            best_itinerary = temp_itinerary.copy()
    
    # If no complete schedule found with all permutations, try a simpler approach
    if not best_itinerary:
        # Sort friends by end availability (earlier first)
        sorted_friends = sorted(friends, key=lambda x: x["end_avail"])
        
        temp_current_time = current_time
        temp_current_location = current_location
        
        for friend in sorted_friends:
            travel_time = travel_times.get((temp_current_location, friend["location"]), 60)
            earliest_start = max(temp_current_time + travel_time, friend["start_avail"])
            
            if earliest_start + friend["duration"] <= friend["end_avail"]:
                best_itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(earliest_start),
                    "end_time": minutes_to_time(earliest_start + friend["duration"])
                })
                temp_current_time = earliest_start + friend["duration"]
                temp_current_location = friend["location"]
    
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()