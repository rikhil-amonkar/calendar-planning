import json
from itertools import permutations

def time_to_min(t_str):
    """Convert '9:00' or '13:30' to minutes since midnight."""
    if 'AM' in t_str or 'PM' in t_str:
        # format like '9:00AM'
        t_str = t_str.replace('AM', '').replace('PM', '')
        if 'PM' in t_str:
            # Actually already removed, need original check
            pass
        # Let's handle properly
        parts = t_str.split()
        if len(parts) == 2:
            t, ampm = parts
        else:
            # Assume no space
            if 'AM' in t_str:
                t = t_str.replace('AM', '')
                ampm = 'AM'
            else:
                t = t_str.replace('PM', '')
                ampm = 'PM'
        h, m = map(int, t.split(':'))
        if ampm == 'PM' and h != 12:
            h += 12
        if ampm == 'AM' and h == 12:
            h = 0
        return h * 60 + m
    else:
        # 24-hour format already
        h, m = map(int, t_str.split(':'))
        return h * 60 + m

def min_to_time(m):
    """Convert minutes since midnight to 'H:MM' format."""
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times dictionary
travel = {
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 9,
}

# Friends data: name, location, window_start, window_end, min_duration
friends = [
    ("Amanda", "Marina District", time_to_min("2:45 PM"), time_to_min("7:30 PM"), 105),
    ("Melissa", "The Castro", time_to_min("9:30 AM"), time_to_min("5:00 PM"), 30),
    ("Jeffrey", "Fisherman's Wharf", time_to_min("12:45 PM"), time_to_min("6:45 PM"), 120),
    ("Matthew", "Bayview", time_to_min("10:15 AM"), time_to_min("1:15 PM"), 30),
    ("Nancy", "Pacific Heights", time_to_min("5:00 PM"), time_to_min("9:30 PM"), 105),
    ("Karen", "Mission District", time_to_min("5:30 PM"), time_to_min("8:30 PM"), 105),
    ("Robert", "Alamo Square", time_to_min("11:15 AM"), time_to_min("5:30 PM"), 120),
    ("Joseph", "Golden Gate Park", time_to_min("8:30 AM"), time_to_min("9:15 PM"), 105),
]

# Start
start_loc = "Presidio"
start_time = time_to_min("9:00 AM")

best_count = 0
best_total_time = 0
best_schedule = []

def dfs(current_loc, current_time, visited, schedule, count, total_meet_time):
    global best_count, best_total_time, best_schedule
    
    # Try to add any unvisited friend
    for idx, (name, loc, win_start, win_end, min_dur) in enumerate(friends):
        if visited & (1 << idx):
            continue
        
        # Travel time
        travel_time = travel[(current_loc, loc)]
        arrival = current_time + travel_time
        
        # Can we meet?
        # We must start by win_end - min_dur at latest
        latest_start = win_end - min_dur
        if arrival > latest_start:
            continue
        
        start_meeting = max(arrival, win_start)
        end_meeting = start_meeting + min_dur
        if end_meeting > win_end:
            continue
        
        # Schedule this friend
        new_schedule = schedule + [(name, loc, start_meeting, end_meeting)]
        new_visited = visited | (1 << idx)
        dfs(loc, end_meeting, new_visited, new_schedule, count + 1, total_meet_time + min_dur)
    
    # No more friends can be added
    if count > best_count or (count == best_count and total_meet_time > best_total_time):
        best_count = count
        best_total_time = total_meet_time
        best_schedule = schedule

# Run DFS
dfs(start_loc, start_time, 0, [], 0, 0)

# Convert to required JSON format
itinerary = []
for name, loc, start_m, end_m in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": min_to_time(start_m),
        "end_time": min_to_time(end_m)
    })

# Output
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))