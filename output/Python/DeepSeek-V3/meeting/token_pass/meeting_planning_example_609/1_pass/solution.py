import itertools
import json

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times in minutes
travel = {
    ('Chinatown', 'Mission District'): 18,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Presidio'): 19,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Presidio'): 25,
    ('Alamo Square', 'Chinatown'): 16,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Presidio'): 18,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Presidio'): 11,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'Presidio'): 24,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Presidio'): 16,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Sunset District'): 15,
}

# Friend data: name, location, window start, window end, min duration
friends = [
    ('David', 'Mission District', '8:00', '19:45', 45),
    ('Kenneth', 'Alamo Square', '14:00', '19:45', 120),
    ('John', 'Pacific Heights', '17:00', '20:00', 15),
    ('Charles', 'Union Square', '21:45', '22:45', 60),
    ('Deborah', 'Golden Gate Park', '7:00', '18:15', 90),
    ('Karen', 'Sunset District', '17:45', '21:15', 15),
    # Carol is impossible, so exclude
]

# Exclude Carol (impossible) and Presidio
friends = [f for f in friends if f[1] != 'Presidio']

# Convert times to minutes
friends_min = []
for name, loc, start, end, dur in friends:
    friends_min.append((name, loc, time_to_minutes(start), time_to_minutes(end), dur))

# Start at Chinatown at 9:00
start_time = time_to_minutes('9:00')
start_loc = 'Chinatown'

best_count = 0
best_schedule = []

# Try all permutations of the 6 friends
for perm in itertools.permutations(friends_min):
    current_time = start_time
    current_loc = start_loc
    schedule = []
    possible = True
    
    for name, loc, win_start, win_end, dur in perm:
        # Travel to friend's location
        travel_time = travel.get((current_loc, loc))
        if travel_time is None:
            # Should not happen
            possible = False
            break
        
        arrive_time = current_time + travel_time
        
        # Start meeting at max(arrive_time, win_start)
        meet_start = max(arrive_time, win_start)
        
        # Check if we can meet for min duration before win_end
        if meet_start + dur > win_end:
            possible = False
            break
        
        meet_end = meet_start + dur
        schedule.append((name, loc, meet_start, meet_end))
        
        # Update current time and location
        current_time = meet_end
        current_loc = loc
    
    if possible and len(schedule) > best_count:
        best_count = len(schedule)
        best_schedule = schedule

# Convert best schedule to output format
itinerary = []
for name, loc, start_m, end_m in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": minutes_to_time(start_m),
        "end_time": minutes_to_time(end_m)
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))