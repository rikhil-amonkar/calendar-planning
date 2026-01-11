import json
import itertools

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times in minutes
travel = {
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Financial District'): 19,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Financial District'): 11,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Financial District'): 8,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'North Beach'): 7,
}

# Friend data: name, location, window start, window end, min duration (minutes)
friends = [
    ('Joseph', 'Russian Hill', time_to_minutes('8:30'), time_to_minutes('19:15'), 60),
    ('Nancy', 'Alamo Square', time_to_minutes('11:00'), time_to_minutes('16:00'), 90),
    ('Jason', 'North Beach', time_to_minutes('16:45'), time_to_minutes('21:45'), 15),
    ('Jeffrey', 'Financial District', time_to_minutes('10:30'), time_to_minutes('15:45'), 45),
]

# Start at Bayview at 9:00
start_location = 'Bayview'
start_time = time_to_minutes('9:00')

best_schedule = []
best_count = 0
best_end_time = float('inf')

# Try all subsets of friends (size 4 down to 1)
for k in range(4, 0, -1):
    for subset in itertools.combinations(range(4), k):
        for perm in itertools.permutations(subset):
            current_location = start_location
            current_time = start_time
            schedule = []
            feasible = True
            
            for idx in perm:
                name, loc, win_start, win_end, dur = friends[idx]
                travel_time = travel[(current_location, loc)]
                arrival = current_time + travel_time
                
                # If we arrive after their window ends, impossible
                if arrival > win_end:
                    feasible = False
                    break
                
                # Start meeting at max(arrival, win_start)
                meet_start = max(arrival, win_start)
                meet_end = meet_start + dur
                
                # If meeting ends after their window ends, impossible
                if meet_end > win_end:
                    feasible = False
                    break
                
                schedule.append((name, loc, meet_start, meet_end))
                current_location = loc
                current_time = meet_end
            
            if feasible:
                if len(schedule) > best_count:
                    best_count = len(schedule)
                    best_schedule = schedule
                    best_end_time = current_time
                elif len(schedule) == best_count and current_time < best_end_time:
                    # Tie-break: earlier finish
                    best_schedule = schedule
                    best_end_time = current_time
            
            # If we already found a schedule with 4 friends, stop searching smaller subsets
            if best_count == 4:
                break
        if best_count == 4:
            break
    if best_count == 4:
        break

# Convert best_schedule to required JSON format
itinerary = []
for name, loc, meet_start, meet_end in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": minutes_to_time(meet_start),
        "end_time": minutes_to_time(meet_end)
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))