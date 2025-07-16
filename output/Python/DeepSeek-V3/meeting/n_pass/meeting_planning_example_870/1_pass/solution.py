import json
from itertools import permutations

# Convert time string to minutes since 9:00 (540 minutes)
def time_to_min(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m - 540  # 9:00 is 0

# Convert minutes since 9:00 back to time string
def min_to_time(minutes):
    total_min = minutes + 540
    h = total_min // 60
    m = total_min % 60
    return f"{h}:{m:02d}"

# Travel time lookup
travel_times = {
    'Pacific Heights': {
        'Marina District': 6, 'The Castro': 16, 'Richmond District': 12, 'Alamo Square': 10,
        'Financial District': 13, 'Presidio': 11, 'Mission District': 15, 'Nob Hill': 8, 'Russian Hill': 7
    },
    'Marina District': {
        'Pacific Heights': 7, 'The Castro': 22, 'Richmond District': 11, 'Alamo Square': 15,
        'Financial District': 17, 'Presidio': 10, 'Mission District': 20, 'Nob Hill': 12, 'Russian Hill': 8
    },
    'The Castro': {
        'Pacific Heights': 16, 'Marina District': 21, 'Richmond District': 16, 'Alamo Square': 8,
        'Financial District': 21, 'Presidio': 20, 'Mission District': 7, 'Nob Hill': 16, 'Russian Hill': 18
    },
    'Richmond District': {
        'Pacific Heights': 10, 'Marina District': 9, 'The Castro': 16, 'Alamo Square': 13,
        'Financial District': 22, 'Presidio': 7, 'Mission District': 20, 'Nob Hill': 17, 'Russian Hill': 13
    },
    'Alamo Square': {
        'Pacific Heights': 10, 'Marina District': 15, 'The Castro': 8, 'Richmond District': 11,
        'Financial District': 17, 'Presidio': 17, 'Mission District': 10, 'Nob Hill': 11, 'Russian Hill': 13
    },
    'Financial District': {
        'Pacific Heights': 13, 'Marina District': 15, 'The Castro': 20, 'Richmond District': 21,
        'Alamo Square': 17, 'Presidio': 22, 'Mission District': 17, 'Nob Hill': 8, 'Russian Hill': 11
    },
    'Presidio': {
        'Pacific Heights': 11, 'Marina District': 11, 'The Castro': 21, 'Richmond District': 7,
        'Alamo Square': 19, 'Financial District': 23, 'Mission District': 26, 'Nob Hill': 18, 'Russian Hill': 14
    },
    'Mission District': {
        'Pacific Heights': 16, 'Marina District': 19, 'The Castro': 7, 'Richmond District': 20,
        'Alamo Square': 11, 'Financial District': 15, 'Presidio': 25, 'Nob Hill': 12, 'Russian Hill': 15
    },
    'Nob Hill': {
        'Pacific Heights': 8, 'Marina District': 11, 'The Castro': 17, 'Richmond District': 14,
        'Alamo Square': 11, 'Financial District': 9, 'Presidio': 17, 'Mission District': 13, 'Russian Hill': 5
    },
    'Russian Hill': {
        'Pacific Heights': 7, 'Marina District': 7, 'The Castro': 21, 'Richmond District': 14,
        'Alamo Square': 15, 'Financial District': 11, 'Presidio': 14, 'Mission District': 16, 'Nob Hill': 5
    }
}

# People data: name, location, available start, available end, min duration
people = [
    ('Linda', 'Marina District', time_to_min('18:00'), time_to_min('22:00'), 30),
    ('Kenneth', 'The Castro', time_to_min('14:45'), time_to_min('16:15'), 30),
    ('Kimberly', 'Richmond District', time_to_min('14:15'), time_to_min('22:00'), 30),
    ('Paul', 'Alamo Square', time_to_min('21:00'), time_to_min('21:30'), 15),
    ('Carol', 'Financial District', time_to_min('10:15'), time_to_min('12:00'), 60),
    ('Brian', 'Presidio', time_to_min('10:00'), time_to_min('21:30'), 75),
    ('Laura', 'Mission District', time_to_min('16:15'), time_to_min('20:30'), 30),
    ('Sandra', 'Nob Hill', time_to_min('9:15'), time_to_min('18:30'), 60),
    ('Karen', 'Russian Hill', time_to_min('18:30'), time_to_min('22:00'), 75)
]

def get_travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
    try:
        return travel_times[from_loc][to_loc]
    except KeyError:
        return travel_times[to_loc][from_loc]

def schedule_meeting(current_time, current_location, person):
    name, loc, start, end, duration = person
    
    # Calculate earliest possible start time (after travel)
    travel_time = get_travel_time(current_location, loc)
    earliest_start = current_time + travel_time
    
    # Check if we can meet within their availability
    meeting_start = max(earliest_start, start)
    if meeting_start + duration > end:
        return None  # Can't meet this person
    
    return {
        'start': meeting_start,
        'end': meeting_start + duration,
        'location': loc,
        'person': name
    }

def evaluate_schedule(order):
    current_time = 0  # 9:00
    current_location = 'Pacific Heights'
    itinerary = []
    
    for idx in order:
        person = people[idx]
        meeting = schedule_meeting(current_time, current_location, person)
        if not meeting:
            return None
        
        itinerary.append(meeting)
        current_time = meeting['end']
        current_location = meeting['location']
    
    return itinerary

def find_best_schedule():
    best_schedule = None
    best_count = 0
    
    # Try all possible orders (but limit to 5 people to keep computation reasonable)
    for perm in permutations(range(len(people)), 5):
        schedule = evaluate_schedule(perm)
        if schedule and len(schedule) > best_count:
            best_schedule = schedule
            best_count = len(schedule)
    
    # If no full schedule found, try with fewer people
    if best_count < len(people):
        for perm in permutations(range(len(people)), best_count + 1):
            schedule = evaluate_schedule(perm)
            if schedule and len(schedule) > best_count:
                best_schedule = schedule
                best_count = len(schedule)
    
    return best_schedule

def main():
    best = find_best_schedule()
    
    if not best:
        print(json.dumps({"itinerary": []}))
        return
    
    itinerary = []
    for meeting in best:
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": min_to_time(meeting['start']),
            "end_time": min_to_time(meeting['end'])
        })
    
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()