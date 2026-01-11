import json
from itertools import permutations
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

# Travel times in minutes
travel_times = {
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Alamo Square"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Union Square"): 14,
}

# Friends data: location, window start, window end, min duration
friends = {
    "Sarah": {"location": "North Beach", "start": "16:00", "end": "18:15", "min_duration": 60},
    "Jeffrey": {"location": "Union Square", "start": "15:00", "end": "22:00", "min_duration": 75},
    "Brian": {"location": "Alamo Square", "start": "16:00", "end": "17:30", "min_duration": 75},
}

# Start location and time
start_location = "Sunset District"
start_time = time_to_minutes("9:00")

def try_schedule(order):
    """Try to schedule meetings in given order, return total meeting minutes and itinerary if valid."""
    current_location = start_location
    current_time = start_time
    itinerary = []
    total_meeting_time = 0
    
    for person in order:
        info = friends[person]
        loc = info["location"]
        win_start = time_to_minutes(info["start"])
        win_end = time_to_minutes(info["end"])
        min_dur = info["min_duration"]
        
        # Travel to this friend's location
        travel_key = (current_location, loc)
        travel = travel_times.get(travel_key, float('inf'))
        arrival = current_time + travel
        
        # If we arrive before window start, wait
        if arrival < win_start:
            arrival = win_start
        
        # Check if we can meet for min_duration before window ends
        if arrival + min_dur > win_end:
            return 0, []  # Not possible
        
        # Schedule the meeting
        meeting_end = arrival + min_dur
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": minutes_to_time(arrival),
            "end_time": minutes_to_time(meeting_end)
        })
        
        total_meeting_time += min_dur
        current_location = loc
        current_time = meeting_end
    
    return total_meeting_time, itinerary

def main():
    best_total = 0
    best_itinerary = []
    
    # Try all permutations of meetings
    for perm in permutations(friends.keys()):
        total, itinerary = try_schedule(perm)
        if total > best_total:
            best_total = total
            best_itinerary = itinerary
    
    # Output as JSON
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()