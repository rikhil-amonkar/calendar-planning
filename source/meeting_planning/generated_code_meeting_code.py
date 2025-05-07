import itertools

def time_str(minutes):
    hour = minutes // 60
    min = minutes % 60
    if hour == 0:
        return f"12:{min:02}AM"
    elif hour < 12:
        return f"{hour}:{min:02}AM"
    else:
        hour_12 = hour % 12
        if hour_12 == 0:
            hour_12 = 12
        return f"{hour_12}:{min:02}PM"

travel_times = {
    'Bayview': {
        'Pacific Heights': 23,
        'Mission District': 13,
        'Haight-Ashbury': 19,
        'Financial District': 19,
    },
    'Pacific Heights': {
        'Bayview': 22,
        'Mission District': 15,
        'Haight-Ashbury': 11,
        'Financial District': 13,
    },
    'Mission District': {
        'Bayview': 15,
        'Pacific Heights': 16,
        'Haight-Ashbury': 12,
        'Financial District': 17,
    },
    'Haight-Ashbury': {
        'Bayview': 18,
        'Pacific Heights': 12,
        'Mission District': 11,
        'Financial District': 21,
    },
    'Financial District': {
        'Bayview': 19,
        'Pacific Heights': 13,
        'Mission District': 17,
        'Haight-Ashbury': 19,
    }
}

friends = [
    {
        'name': 'Mary',
        'location': 'Pacific Heights',
        'start': 600,  # 10:00 AM
        'end': 1140,   # 7:00 PM
        'duration': 45
    },
    {
        'name': 'Lisa',
        'location': 'Mission District',
        'start': 1260, # 8:30 PM
        'end': 1380,   # 10:00 PM
        'duration': 75
    },
    {
        'name': 'Betty',
        'location': 'Haight-Ashbury',
        'start': 435,  # 7:15 AM
        'end': 975,    # 5:15 PM
        'duration': 90
    },
    {
        'name': 'Charles',
        'location': 'Financial District',
        'start': 675,  # 11:15 AM
        'end': 810,    # 3:00 PM
        'duration': 120
    }
]

def simulate(order):
    current_time = 540  # 9:00 AM
    current_location = 'Bayview'
    schedule = []
    schedule.append({'action': 'start', 'location': current_location, 'time': time_str(current_time)})
    
    for friend in order:
        # Travel to friend's location
        travel_duration = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_duration
        
        if arrival_time > friend['end']:
            return None  # Cannot meet this friend
        
        meeting_start = max(arrival_time, friend['start'])
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > friend['end']:
            return None  # Cannot meet for required duration
        
        # Add travel action
        schedule.append({
            'action': 'travel',
            'location': current_location,
            'duration': travel_duration,
            'time': time_str(current_time),
            'to': friend['location']
        })
        
        # Check if waiting is needed
        if meeting_start > arrival_time:
            wait_duration = meeting_start - arrival_time
            schedule.append({
                'action': 'wait',
                'location': friend['location'],
                'time': time_str(arrival_time)
            })
        
        # Add meet action
        schedule.append({
            'action': 'meet',
            'location': friend['location'],
            'duration': friend['duration'],
            'time': time_str(meeting_start)
        })
        
        # Update current time and location
        current_time = meeting_end
        current_location = friend['location']
    
    return schedule

best_schedule = None
max_friends = 0

for n in range(len(friends), 0, -1):
    for combo in itertools.combinations(friends, n):
        for perm in itertools.permutations(combo):
            schedule = simulate(perm)
            if schedule and len(schedule) > max_friends:
                best_schedule = schedule
                max_friends = len(schedule)
                if max_friends == len(friends):
                    break
        if max_friends == len(friends):
            break
    if max_friends == len(friends):
        break

print('SOLUTION:')
print({'schedule': best_schedule})