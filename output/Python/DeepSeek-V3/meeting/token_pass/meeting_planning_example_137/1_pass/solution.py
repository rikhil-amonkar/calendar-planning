import json
from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    elif isinstance(t, datetime):
        return t.hour * 60 + t.minute
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

def add_minutes_to_time(t_str, delta_minutes):
    m = time_to_minutes(t_str) + delta_minutes
    return minutes_to_time(m)

def schedule_meetings():
    # Travel times matrix (in minutes)
    travel = {
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Golden Gate Park"): 23,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Chinatown"): 23,
    }
    
    # Constraints
    start_location = "Financial District"
    start_time_str = "9:00"
    
    friends = [
        {
            "name": "Kenneth",
            "location": "Chinatown",
            "window_start": "12:00",
            "window_end": "15:00",
            "min_duration": 90,
        },
        {
            "name": "Barbara",
            "location": "Golden Gate Park",
            "window_start": "8:15",
            "window_end": "19:00",
            "min_duration": 45,
        }
    ]
    
    # Try both permutations of meeting order
    from itertools import permutations
    best_schedule = []
    best_meetings_count = 0
    best_total_meeting_time = 0
    
    for perm in permutations(friends):
        current_location = start_location
        current_time = time_to_minutes(start_time_str)
        schedule = []
        meetings_count = 0
        total_meeting_time = 0
        
        for friend in perm:
            # Travel to friend's location
            travel_key = (current_location, friend["location"])
            travel_time = travel[travel_key]
            arrival_time = current_time + travel_time
            
            # Friend's time window in minutes
            window_start = time_to_minutes(friend["window_start"])
            window_end = time_to_minutes(friend["window_end"])
            min_duration = friend["min_duration"]
            
            # Check if we can meet within window
            # We can start meeting at max(window_start, arrival_time)
            meeting_start = max(arrival_time, window_start)
            meeting_end = meeting_start + min_duration
            
            if meeting_end <= window_end:
                # Meeting possible
                schedule.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(meeting_start),
                    "end_time": minutes_to_time(meeting_end),
                })
                meetings_count += 1
                total_meeting_time += min_duration
                current_location = friend["location"]
                current_time = meeting_end
            else:
                # Cannot meet this friend in this order
                break
        
        # Evaluate this permutation
        if meetings_count > best_meetings_count or \
           (meetings_count == best_meetings_count and total_meeting_time > best_total_meeting_time):
            best_meetings_count = meetings_count
            best_total_meeting_time = total_meeting_time
            best_schedule = schedule
    
    return best_schedule

def main():
    itinerary = schedule_meetings()
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()