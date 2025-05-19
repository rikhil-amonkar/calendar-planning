import json
from itertools import permutations

def time_to_minutes(time_str):
    """Convert time string 'H:MM' to minutes since midnight."""
    if isinstance(time_str, str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m
    return time_str

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string 'H:MM'."""
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times dictionary: {from_location: {to_location: minutes}}
travel_times = {
    'Presidio': {
        'Marina District': 11,
        'The Castro': 21,
        'Fisherman\'s Wharf': 19,
        'Bayview': 31,
        'Pacific Heights': 11,
        'Mission District': 26,
        'Alamo Square': 19,
        'Golden Gate Park': 12
    },
    'Marina District': {
        'Presidio': 10,
        'The Castro': 22,
        'Fisherman\'s Wharf': 10,
        'Bayview': 27,
        'Pacific Heights': 7,
        'Mission District': 20,
        'Alamo Square': 15,
        'Golden Gate Park': 18
    },
    'The Castro': {
        'Presidio': 20,
        'Marina District': 21,
        'Fisherman\'s Wharf': 24,
        'Bayview': 19,
        'Pacific Heights': 16,
        'Mission District': 7,
        'Alamo Square': 8,
        'Golden Gate Park': 11
    },
    'Fisherman\'s Wharf': {
        'Presidio': 17,
        'Marina District': 9,
        'The Castro': 27,
        'Bayview': 26,
        'Pacific Heights': 12,
        'Mission District': 22,
        'Alamo Square': 21,
        'Golden Gate Park': 25
    },
    'Bayview': {
        'Presidio': 32,
        'Marina District': 27,
        'The Castro': 19,
        'Fisherman\'s Wharf': 25,
        'Pacific Heights': 23,
        'Mission District': 13,
        'Alamo Square': 16,
        'Golden Gate Park': 22
    },
    'Pacific Heights': {
        'Presidio': 11,
        'Marina District': 6,
        'The Castro': 16,
        'Fisherman\'s Wharf': 13,
        'Bayview': 22,
        'Mission District': 15,
        'Alamo Square': 10,
        'Golden Gate Park': 15
    },
    'Mission District': {
        'Presidio': 25,
        'Marina District': 19,
        'The Castro': 7,
        'Fisherman\'s Wharf': 22,
        'Bayview': 14,
        'Pacific Heights': 16,
        'Alamo Square': 11,
        'Golden Gate Park': 17
    },
    'Alamo Square': {
        'Presidio': 17,
        'Marina District': 15,
        'The Castro': 8,
        'Fisherman\'s Wharf': 19,
        'Bayview': 16,
        'Pacific Heights': 10,
        'Mission District': 10,
        'Golden Gate Park': 9
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Marina District': 16,
        'The Castro': 13,
        'Fisherman\'s Wharf': 24,
        'Bayview': 23,
        'Pacific Heights': 16,
        'Mission District': 17,
        'Alamo Square': 9
    }
}

# Friend constraints: name, location, available_start, available_end, min_duration
friends = [
    ('Amanda', 'Marina District', time_to_minutes('14:45'), time_to_minutes('19:30'), 105),
    ('Melissa', 'The Castro', time_to_minutes('9:30'), time_to_minutes('17:00'), 30),
    ('Jeffrey', 'Fisherman\'s Wharf', time_to_minutes('12:45'), time_to_minutes('18:45'), 120),
    ('Matthew', 'Bayview', time_to_minutes('10:15'), time_to_minutes('13:15'), 30),
    ('Nancy', 'Pacific Heights', time_to_minutes('17:00'), time_to_minutes('21:30'), 105),
    ('Karen', 'Mission District', time_to_minutes('17:30'), time_to_minutes('20:30'), 105),
    ('Robert', 'Alamo Square', time_to_minutes('11:15'), time_to_minutes('17:30'), 120),
    ('Joseph', 'Golden Gate Park', time_to_minutes('8:30'), time_to_minutes('21:15'), 105)
]

def calculate_schedule(order):
    current_time = time_to_minutes('9:00')  # Start at Presidio at 9:00
    current_location = 'Presidio'
    schedule = []
    
    for friend_idx in order:
        name, loc, avail_start, avail_end, min_dur = friends[friend_idx]
        
        # Calculate travel time
        travel_time = travel_times[current_location][loc]
        arrival_time = current_time + travel_time
        
        # Determine meeting window
        meeting_start = max(arrival_time, avail_start)
        meeting_end = min(meeting_start + min_dur, avail_end)
        
        if meeting_end - meeting_start < min_dur:
            return None  # Can't meet minimum duration
        
        schedule.append({
            'action': 'meet',
            'location': loc,
            'person': name,
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = loc
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return 0
    
    # Count number of friends met
    return len(schedule)

def find_optimal_schedule():
    best_schedule = []
    best_score = 0
    
    # Try all possible orders (with some optimizations)
    for order in permutations(range(len(friends))):
        schedule = calculate_schedule(order)
        score = evaluate_schedule(schedule)
        
        if score > best_score:
            best_score = score
            best_schedule = schedule
            if best_score == len(friends):  # Found perfect schedule
                break
    
    return best_schedule

def main():
    optimal_schedule = find_optimal_schedule()
    result = {
        "itinerary": optimal_schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()