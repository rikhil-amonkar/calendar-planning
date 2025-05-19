import json

def time_to_min(t_str):
    time_part, period = t_str[:-2], t_str[-2:]
    hours, mins = map(int, time_part.split(':'))
    if period == 'PM' and hours != 12:
        hours += 12
    elif period == 'AM' and hours == 12:
        hours = 0
    return hours * 60 + mins

def min_to_time(m):
    hours, mins = divmod(m, 60)
    return f"{hours}:{mins:02d}"

friends = [
    {'name': 'Helen', 'location': 'Golden Gate Park', 'available_start': time_to_min('9:30AM'), 'available_end': time_to_min('12:15PM'), 'duration': 45},
    {'name': 'Steven', 'location': 'The Castro', 'available_start': time_to_min('8:15PM'), 'available_end': time_to_min('10:00PM'), 'duration': 105},
    {'name': 'Deborah', 'location': 'Bayview', 'available_start': time_to_min('8:30AM'), 'available_end': time_to_min('12:00PM'), 'duration': 30},
    {'name': 'Matthew', 'location': 'Marina District', 'available_start': time_to_min('9:15AM'), 'available_end': time_to_min('2:15PM'), 'duration': 45},
    {'name': 'Joseph', 'location': 'Union Square', 'available_start': time_to_min('2:15PM'), 'available_end': time_to_min('6:45PM'), 'duration': 120},
    {'name': 'Ronald', 'location': 'Sunset District', 'available_start': time_to_min('4:00PM'), 'available_end': time_to_min('8:45PM'), 'duration': 60},
    {'name': 'Robert', 'location': 'Alamo Square', 'available_start': time_to_min('6:30PM'), 'available_end': time_to_min('9:15PM'), 'duration': 120},
    {'name': 'Rebecca', 'location': 'Financial District', 'available_start': time_to_min('2:45PM'), 'available_end': time_to_min('4:15PM'), 'duration': 30},
    {'name': 'Elizabeth', 'location': 'Mission District', 'available_start': time_to_min('6:30PM'), 'available_end': time_to_min('9:00PM'), 'duration': 120}
]

travel_time = {
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Mission District'): 17,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Mission District'): 7,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Mission District'): 20,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Mission District'): 14,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Mission District'): 25,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Mission District'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Mission District'): 17,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Financial District'): 15
}

best_itinerary = []
max_count = 0

def backtrack(current_time, current_location, visited, itinerary):
    global best_itinerary, max_count
    if len(visited) > max_count:
        best_itinerary = itinerary.copy()
        max_count = len(visited)
    remaining = len(friends) - len(visited)
    if remaining + len(visited) <= max_count:
        return
    for friend in friends:
        name = friend['name']
        if name not in visited:
            from_loc = current_location
            to_loc = friend['location']
            tt = travel_time.get((from_loc, to_loc), 0)
            arrival_time = current_time + tt
            available_start = friend['available_start']
            available_end = friend['available_end']
            start = max(arrival_time, available_start)
            end = start + friend['duration']
            if end <= available_end:
                new_visited = set(visited)
                new_visited.add(name)
                new_itinerary = list(itinerary)
                new_itinerary.append({
                    "action": "meet",
                    "location": to_loc,
                    "person": name,
                    "start_time": min_to_time(start).replace(':0', ':') if mins == 0 else min_to_time(start),
                    "end_time": min_to_time(end).replace(':0', ':') if mins == 0 else min_to_time(end)
                })
                if len(new_visited) + (len(friends) - len(new_visited)) <= max_count:
                    continue
                backtrack(end, to_loc, new_visited, new_itinerary)

backtrack(540, 'Pacific Heights', set(), [])

output = {"itinerary": best_itinerary}
print(json.dumps(output, indent=2))