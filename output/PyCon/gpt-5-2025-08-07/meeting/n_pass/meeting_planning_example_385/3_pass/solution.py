import json
from datetime import datetime, timedelta

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Pacific Heights'): 11,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Pacific Heights'): 8,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13
    }
    
    # Friend constraints: (location, start_min, end_min, duration_min)
    friends = {
        'Jeffrey': ('Presidio', 480, 600, 105),    # 8:00-10:00 AM, 105 min
        'Steven': ('North Beach', 810, 1320, 45),  # 1:30-10:00 PM, 45 min
        'Barbara': ('Fisherman\'s Wharf', 1080, 1290, 30),  # 6:00-9:30 PM, 30 min
        'John': ('Pacific Heights', 540, 810, 15)  # 9:00 AM-1:30 PM, 15 min
    }
    
    # Use an optimized scheduling approach
    itinerary = optimized_schedule(friends, travel_times)
    
    # Output as JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

def optimized_schedule(friends, travel_times):
    """Optimized scheduling that tries to fit all meetings"""
    
    # Start at Nob Hill at 9:00 AM (540 minutes)
    current_time = 540
    current_location = 'Nob Hill'
    scheduled = set()
    itinerary = []
    
    # Try different orders to find one that fits all meetings
    orders_to_try = [
        ['John', 'Jeffrey', 'Steven', 'Barbara'],  # Chronological by availability start
        ['John', 'Jeffrey', 'Barbara', 'Steven'],  # Different combination
        ['Jeffrey', 'John', 'Steven', 'Barbara'],  # Another combination
        ['John', 'Steven', 'Barbara', 'Jeffrey']   # Another combination
    ]
    
    best_itinerary = []
    max_meetings = 0
    
    for order in orders_to_try:
        current_time = 540
        current_location = 'Nob Hill'
        temp_itinerary = []
        temp_scheduled = set()
        
        for friend in order:
            if friend in temp_scheduled:
                continue
                
            location, friend_start, friend_end, duration = friends[friend]
            
            # Calculate travel time to this location
            travel_time = travel_times.get((current_location, location), 0)
            
            # Earliest we can start this meeting
            earliest_start = max(current_time + travel_time, friend_start)
            
            # Check if we can fit this meeting
            if earliest_start + duration <= friend_end:
                start_time_str = minutes_to_time(earliest_start)
                end_time_str = minutes_to_time(earliest_start + duration)
                
                temp_itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": friend,
                    "start_time": start_time_str,
                    "end_time": end_time_str
                })
                
                temp_scheduled.add(friend)
                current_time = earliest_start + duration
                current_location = location
        
        # Check if this order scheduled more meetings
        if len(temp_scheduled) > max_meetings:
            max_meetings = len(temp_scheduled)
            best_itinerary = temp_itinerary.copy()
            
        # If we found a schedule with all 4 meetings, we're done
        if len(temp_scheduled) == 4:
            break
    
    # If we still don't have all meetings, try a more flexible approach
    if max_meetings < 4:
        best_itinerary = flexible_schedule(friends, travel_times)
    
    # Sort by start time
    best_itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
    return best_itinerary

def flexible_schedule(friends, travel_times):
    """More flexible scheduling that tries different combinations"""
    
    # Try to schedule Jeffrey first (he has the earliest end time)
    current_time = 540  # 9:00 AM
    current_location = 'Nob Hill'
    itinerary = []
    scheduled = set()
    
    # Jeffrey has tight constraints (ends at 10:00 AM)
    jeffrey_loc, jeffrey_start, jeffrey_end, jeffrey_dur = friends['Jeffrey']
    travel_to_jeffrey = travel_times.get((current_location, jeffrey_loc), 0)
    
    # Can we make it to Jeffrey?
    jeffrey_earliest = max(current_time + travel_to_jeffrey, jeffrey_start)
    if jeffrey_earliest + jeffrey_dur <= jeffrey_end:
        # Schedule Jeffrey
        itinerary.append({
            "action": "meet",
            "location": jeffrey_loc,
            "person": 'Jeffrey',
            "start_time": minutes_to_time(jeffrey_earliest),
            "end_time": minutes_to_time(jeffrey_earliest + jeffrey_dur)
        })
        scheduled.add('Jeffrey')
        current_time = jeffrey_earliest + jeffrey_dur
        current_location = jeffrey_loc
    
    # Now try John (he's available 9:00 AM - 1:30 PM)
    if 'John' not in scheduled:
        john_loc, john_start, john_end, john_dur = friends['John']
        travel_to_john = travel_times.get((current_location, john_loc), 0)
        john_earliest = max(current_time + travel_to_john, john_start)
        
        if john_earliest + john_dur <= john_end:
            itinerary.append({
                "action": "meet",
                "location": john_loc,
                "person": 'John',
                "start_time": minutes_to_time(john_earliest),
                "end_time": minutes_to_time(john_earliest + john_dur)
            })
            scheduled.add('John')
            current_time = john_earliest + john_dur
            current_location = john_loc
    
    # Now try Steven (1:30 PM - 10:00 PM)
    if 'Steven' not in scheduled:
        steven_loc, steven_start, steven_end, steven_dur = friends['Steven']
        travel_to_steven = travel_times.get((current_location, steven_loc), 0)
        steven_earliest = max(current_time + travel_to_steven, steven_start)
        
        if steven_earliest + steven_dur <= steven_end:
            itinerary.append({
                "action": "meet",
                "location": steven_loc,
                "person": 'Steven',
                "start_time": minutes_to_time(steven_earliest),
                "end_time": minutes_to_time(steven_earliest + steven_dur)
            })
            scheduled.add('Steven')
            current_time = steven_earliest + steven_dur
            current_location = steven_loc
    
    # Finally try Barbara (6:00 PM - 9:30 PM)
    if 'Barbara' not in scheduled:
        barbara_loc, barbara_start, barbara_end, barbara_dur = friends['Barbara']
        travel_to_barbara = travel_times.get((current_location, barbara_loc), 0)
        barbara_earliest = max(current_time + travel_to_barbara, barbara_start)
        
        if barbara_earliest + barbara_dur <= barbara_end:
            itinerary.append({
                "action": "meet",
                "location": barbara_loc,
                "person": 'Barbara',
                "start_time": minutes_to_time(barbara_earliest),
                "end_time": minutes_to_time(barbara_earliest + barbara_dur)
            })
            scheduled.add('Barbara')
    
    return itinerary

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    if isinstance(time_str, int):
        return time_str
    
    time_obj = datetime.strptime(time_str, '%H:%M')
    return time_obj.hour * 60 + time_obj.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

if __name__ == "__main__":
    main()