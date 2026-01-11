import json
from itertools import permutations
from datetime import datetime, timedelta

def parse_time(timestr):
    """Convert 'H:MMAM/PM' to datetime today for easier arithmetic."""
    # Input like '9:00AM' or '7:45PM'
    timestr = timestr.strip()
    if 'AM' in timestr:
        hour_min = timestr.replace('AM', '').split(':')
        hour = int(hour_min[0])
        if hour == 12:
            hour = 0
    else:
        hour_min = timestr.replace('PM', '').split(':')
        hour = int(hour_min[0])
        if hour != 12:
            hour += 12
    minute = int(hour_min[1])
    return datetime(2025, 1, 1, hour, minute)

def format_time(dt):
    """Convert datetime to 'H:MM' 24-hour format."""
    return f"{dt.hour}:{dt.minute:02d}"

# Travel times in minutes between locations
travel_times = {
    ('Fisherman\'s Wharf', 'The Castro'): 26,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'North Beach'): 20,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'North Beach'): 5,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'North Beach'): 5,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'North Beach'): 8,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'North Beach'): 15,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Alamo Square'): 16,
}

# Friend data: name, location, window start, window end, min duration
friends = [
    ('Laura', 'The Castro', '7:45PM', '9:30PM', 105),
    ('Daniel', 'Golden Gate Park', '9:15PM', '9:45PM', 15),
    ('William', 'Embarcadero', '7:00AM', '9:00AM', 90),
    ('Karen', 'Russian Hill', '2:30PM', '7:45PM', 30),
    ('Stephanie', 'Nob Hill', '7:30AM', '9:30AM', 45),
    ('Joseph', 'Alamo Square', '11:30AM', '12:45PM', 15),
    ('Kimberly', 'North Beach', '3:45PM', '7:15PM', 30),
]

# Convert times
friends_converted = []
for name, loc, start_str, end_str, dur in friends:
    start_t = parse_time(start_str)
    end_t = parse_time(end_str)
    friends_converted.append((name, loc, start_t, end_t, dur))

# Start at Fisherman's Wharf at 9:00 AM
current_time = parse_time('9:00AM')
current_location = 'Fisherman\'s Wharf'

# Filter impossible friends (window ends before we can arrive with min duration)
feasible = []
for name, loc, start_t, end_t, min_dur in friends_converted:
    travel = travel_times.get((current_location, loc), 60)  # default high if missing
    earliest_arrive = current_time + timedelta(minutes=travel)
    if earliest_arrive < end_t and (end_t - max(earliest_arrive, start_t)).seconds >= min_dur * 60:
        feasible.append((name, loc, start_t, end_t, min_dur))

# We'll search permutations of feasible friends
best_schedule = []
best_count = 0

# Try all permutations of up to all feasible friends
feasible_names = [f[0] for f in feasible]
feasible_dict = {f[0]: f for f in feasible}

for perm in permutations(feasible_names):
    schedule = []
    current_loc = 'Fisherman\'s Wharf'
    current_time_val = parse_time('9:00AM')
    possible = True
    for name in perm:
        _, loc, start_t, end_t, min_dur = feasible_dict[name]
        travel = travel_times.get((current_loc, loc), 60)
        arrive = current_time_val + timedelta(minutes=travel)
        # If arrive before start, wait
        meet_start = max(arrive, start_t)
        if meet_start + timedelta(minutes=min_dur) > end_t:
            possible = False
            break
        meet_end = meet_start + timedelta(minutes=min_dur)
        schedule.append((name, loc, meet_start, meet_end))
        current_loc = loc
        current_time_val = meet_end
    if possible and len(schedule) > best_count:
        best_count = len(schedule)
        best_schedule = schedule

# Convert best_schedule to itinerary format
itinerary = []
for name, loc, start_t, end_t in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": format_time(start_t),
        "end_time": format_time(end_t)
    })

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))