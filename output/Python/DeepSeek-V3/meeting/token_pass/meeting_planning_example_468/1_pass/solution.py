import json
import itertools
from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes from midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from midnight to 'H:MM' string."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times matrix (in minutes)
travel = {
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Bayview', 'The Castro'): 20,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Fisherman\'s Wharf', 'The Castro'): 26,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
}

# People data: name, location, window start, window end (in minutes from midnight)
people = [
    ('Rebecca', 'Bayview', time_to_minutes('9:00'), time_to_minutes('12:45')),
    ('Amanda', 'Pacific Heights', time_to_minutes('18:30'), time_to_minutes('21:45')),
    ('James', 'Alamo Square', time_to_minutes('9:45'), time_to_minutes('21:15')),
    ('Sarah', 'Fisherman\'s Wharf', time_to_minutes('8:00'), time_to_minutes('21:30')),
    ('Melissa', 'Golden Gate Park', time_to_minutes('9:00'), time_to_minutes('18:45')),
]

meeting_duration = 90  # minutes

def schedule_meetings(order):
    """Try to schedule meetings in given order, return itinerary if feasible."""
    current_location = 'The Castro'
    current_time = time_to_minutes('9:00')  # start time
    itinerary = []
    
    for person_name, location, win_start, win_end in order:
        # Travel to location
        travel_time = travel.get((current_location, location))
        if travel_time is None:
            # Should not happen given complete matrix
            return None
        arrival_time = current_time + travel_time
        
        # If we arrive before window start, wait
        start_meeting = max(arrival_time, win_start)
        # If we start too late to get 90 min, fail
        if start_meeting + meeting_duration > win_end:
            return None
        
        # Add meeting
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': person_name,
            'start_time': minutes_to_time(start_meeting),
            'end_time': minutes_to_time(start_meeting + meeting_duration)
        })
        
        # Update current location and time
        current_location = location
        current_time = start_meeting + meeting_duration
    
    return itinerary

# Try all permutations to maximize number of meetings
best_itinerary = []
best_count = 0

# We'll try meeting all 5 first, then if impossible, try 4, etc.
for k in range(5, 0, -1):
    found = False
    for perm in itertools.permutations(people, k):
        # Check if this permutation is feasible
        itinerary = schedule_meetings(perm)
        if itinerary:
            if k > best_count:
                best_count = k
                best_itinerary = itinerary
                found = True
    # If we found a schedule with k meetings, stop (since we want max meetings)
    if found:
        break

# Output result
result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))