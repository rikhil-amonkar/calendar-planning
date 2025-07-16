import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (from_location, to_location): time
travel_times = {
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Sunset District'): 27,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Sunset District'): 24,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Sunset District'): 23,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Sunset District'): 19,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Sunset District'): 27,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Mission District'): 17,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Sunset District'): 29,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Sunset District'): 21,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Sunset District'): 17,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 24,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Nob Hill'): 27
}

# Friend data: name, location, available_start, available_end, min_duration
friends = [
    ('Kevin', 'Mission District', '20:45', '21:45', 60),
    ('Mark', 'Fisherman\'s Wharf', '17:15', '20:00', 90),
    ('Jessica', 'Russian Hill', '9:00', '15:00', 120),
    ('Jason', 'Marina District', '15:15', '21:45', 120),
    ('John', 'North Beach', '9:45', '18:00', 15),
    ('Karen', 'Chinatown', '16:45', '19:00', 75),
    ('Sarah', 'Pacific Heights', '17:30', '18:15', 45),
    ('Amanda', 'The Castro', '20:00', '21:15', 60),
    ('Nancy', 'Nob Hill', '9:45', '13:00', 45),
    ('Rebecca', 'Sunset District', '8:45', '15:00', 75)
]

def get_travel_time(from_loc, to_loc):
    return travel_times.get((from_loc, to_loc), float('inf'))

def is_schedule_valid(schedule):
    current_time = time_to_minutes('9:00')
    current_location = 'Union Square'
    
    for entry in schedule:
        name, location, avail_start, avail_end, min_duration = entry
        travel_time = get_travel_time(current_location, location)
        
        # Arrival time at friend's location
        arrival_time = current_time + travel_time
        avail_start_min = time_to_minutes(avail_start)
        avail_end_min = time_to_minutes(avail_end)
        
        # Can't arrive after availability ends
        if arrival_time > avail_end_min:
            return False
        
        # Start time is max of arrival time and friend's available start
        start_time = max(arrival_time, avail_start_min)
        
        # End time is start time + min_duration
        end_time = start_time + min_duration
        
        # Can't exceed friend's availability
        if end_time > avail_end_min:
            return False
        
        current_time = end_time
        current_location = location
    
    return True

def calculate_total_meeting_time(schedule):
    total = 0
    for entry in schedule:
        total += entry[4]  # min_duration
    return total

def generate_schedules():
    # Try different permutations of friends to find a valid schedule
    # We'll limit to permutations of 5 friends to keep computation reasonable
    from itertools import combinations
    best_schedule = []
    best_time = 0
    
    for friend_count in range(5, 6):
        for friend_group in combinations(friends, friend_count):
            for perm in permutations(friend_group):
                if is_schedule_valid(perm):
                    total_time = calculate_total_meeting_time(perm)
                    if total_time > best_time:
                        best_time = total_time
                        best_schedule = perm
                        # Early exit if we find a schedule with all friends
                        if len(best_schedule) == len(friends):
                            return best_schedule
    
    return best_schedule

def build_itinerary(schedule):
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'Union Square'
    
    for entry in schedule:
        name, location, _, _, min_duration = entry
        travel_time = get_travel_time(current_location, location)
        
        # Travel action
        if travel_time > 0:
            travel_start = minutes_to_time(current_time)
            current_time += travel_time
            travel_end = minutes_to_time(current_time)
            itinerary.append({
                "action": "travel",
                "from": current_location,
                "to": location,
                "start_time": travel_start,
                "end_time": travel_end
            })
        
        # Meeting action
        avail_start_min = time_to_minutes(entry[2])
        start_time = max(current_time, avail_start_min)
        end_time = start_time + min_duration
        
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": name,
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        
        current_time = end_time
        current_location = location
    
    return itinerary

# Generate the best schedule
best_schedule = generate_schedules()

if not best_schedule:
    print(json.dumps({"error": "No valid schedule found"}))
else:
    itinerary = build_itinerary(best_schedule)
    print(json.dumps({"itinerary": itinerary}, indent=2))