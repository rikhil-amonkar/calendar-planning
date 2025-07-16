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
    # ... (rest of travel times remain the same)
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
        
        arrival_time = current_time + travel_time
        avail_start_min = time_to_minutes(avail_start)
        avail_end_min = time_to_minutes(avail_end)
        
        if arrival_time > avail_end_min:
            return False
        
        start_time = max(arrival_time, avail_start_min)
        end_time = start_time + min_duration
        
        if end_time > avail_end_min:
            return False
        
        current_time = end_time
        current_location = location
    
    return True

def calculate_total_meeting_time(schedule):
    return sum(entry[4] for entry in schedule)

def generate_schedules():
    # Prioritize friends with earlier availability and longer durations
    sorted_friends = sorted(friends, key=lambda x: (time_to_minutes(x[2]), -x[4]))
    
    best_schedule = []
    best_time = 0
    
    # Try different permutations with a reasonable limit
    for perm in permutations(sorted_friends, min(6, len(sorted_friends))):
        if is_schedule_valid(perm):
            total_time = calculate_total_meeting_time(perm)
            if total_time > best_time:
                best_time = total_time
                best_schedule = perm
                # Early exit if we find a schedule that meets all friends
                if len(best_schedule) == len(friends):
                    break
    
    return best_schedule

def build_itinerary(schedule):
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'Union Square'
    
    for entry in schedule:
        name, location, avail_start, avail_end, min_duration = entry
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
        avail_start_min = time_to_minutes(avail_start)
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