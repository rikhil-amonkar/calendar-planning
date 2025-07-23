import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Marina District': {
        'Richmond District': 11,
        'Union Square': 16,
        'Nob Hill': 12,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 18,
        'Embarcadero': 14,
        'Financial District': 17,
        'North Beach': 11,
        'Presidio': 10
    },
    'Richmond District': {
        'Marina District': 9,
        'Union Square': 21,
        'Nob Hill': 17,
        'Fisherman\'s Wharf': 18,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Financial District': 22,
        'North Beach': 17,
        'Presidio': 7
    },
    'Union Square': {
        'Marina District': 18,
        'Richmond District': 20,
        'Nob Hill': 9,
        'Fisherman\'s Wharf': 15,
        'Golden Gate Park': 22,
        'Embarcadero': 11,
        'Financial District': 9,
        'North Beach': 10,
        'Presidio': 24
    },
    'Nob Hill': {
        'Marina District': 11,
        'Richmond District': 14,
        'Union Square': 7,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 17,
        'Embarcadero': 9,
        'Financial District': 9,
        'North Beach': 8,
        'Presidio': 17
    },
    'Fisherman\'s Wharf': {
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 13,
        'Nob Hill': 11,
        'Golden Gate Park': 25,
        'Embarcadero': 8,
        'Financial District': 11,
        'North Beach': 6,
        'Presidio': 17
    },
    'Golden Gate Park': {
        'Marina District': 16,
        'Richmond District': 7,
        'Union Square': 22,
        'Nob Hill': 20,
        'Fisherman\'s Wharf': 24,
        'Embarcadero': 25,
        'Financial District': 26,
        'North Beach': 23,
        'Presidio': 11
    },
    'Embarcadero': {
        'Marina District': 12,
        'Richmond District': 21,
        'Union Square': 10,
        'Nob Hill': 10,
        'Fisherman\'s Wharf': 6,
        'Golden Gate Park': 25,
        'Financial District': 5,
        'North Beach': 5,
        'Presidio': 20
    },
    'Financial District': {
        'Marina District': 15,
        'Richmond District': 21,
        'Union Square': 9,
        'Nob Hill': 8,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 23,
        'Embarcadero': 4,
        'North Beach': 7,
        'Presidio': 22
    },
    'North Beach': {
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 7,
        'Nob Hill': 7,
        'Fisherman\'s Wharf': 5,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Financial District': 8,
        'Presidio': 17
    },
    'Presidio': {
        'Marina District': 11,
        'Richmond District': 7,
        'Union Square': 22,
        'Nob Hill': 18,
        'Fisherman\'s Wharf': 19,
        'Golden Gate Park': 12,
        'Embarcadero': 20,
        'Financial District': 23,
        'North Beach': 18
    }
}

# Friend data: name -> (location, start_time, end_time, min_duration_minutes)
friends = {
    'Stephanie': ('Richmond District', (16, 15), (21, 30), 75),
    'William': ('Union Square', (10, 45), (17, 30), 45),
    'Elizabeth': ('Nob Hill', (12, 15), (15, 0), 105),
    'Joseph': ('Fisherman\'s Wharf', (12, 45), (14, 0), 75),
    'Anthony': ('Golden Gate Park', (13, 0), (20, 30), 75),
    'Barbara': ('Embarcadero', (19, 15), (20, 30), 75),
    'Carol': ('Financial District', (11, 45), (16, 15), 60),
    'Sandra': ('North Beach', (10, 0), (12, 30), 15),
    'Kenneth': ('Presidio', (21, 15), (22, 15), 45)
}

def time_to_minutes(time_tuple):
    return time_tuple[0] * 60 + time_tuple[1]

def minutes_to_time(minutes):
    return (minutes // 60, minutes % 60)

def format_time(time_tuple):
    return f"{time_tuple[0]}:{time_tuple[1]:02d}"

def can_schedule_meeting(current_location, current_time, friend_name, itinerary):
    location, (start_h, start_m), (end_h, end_m), duration = friends[friend_name]
    start_time = time_to_minutes((start_h, start_m))
    end_time = time_to_minutes((end_h, end_m))
    
    travel_time = travel_times[current_location][location]
    arrival_time = current_time + travel_time
    
    if arrival_time > end_time:
        return None  # Can't make it in time
    
    meeting_start = max(arrival_time, start_time)
    meeting_end = meeting_start + duration
    
    if meeting_end > end_time:
        return None  # Not enough time
    
    return (location, meeting_start, meeting_end, travel_time)

def evaluate_schedule(order):
    current_location = 'Marina District'
    current_time = time_to_minutes((9, 0))
    itinerary = []
    scheduled_friends = set()
    
    for friend_name in order:
        result = can_schedule_meeting(current_location, current_time, friend_name, itinerary)
        if result is None:
            continue
        
        location, meeting_start, meeting_end, travel_time = result
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': friend_name,
            'start_time': format_time(minutes_to_time(meeting_start)),
            'end_time': format_time(minutes_to_time(meeting_end))
        })
        scheduled_friends.add(friend_name)
        current_location = location
        current_time = meeting_end
    
    # Try to schedule remaining friends
    remaining_friends = set(friends.keys()) - scheduled_friends
    for friend_name in remaining_friends:
        result = can_schedule_meeting(current_location, current_time, friend_name, itinerary)
        if result is None:
            continue
        
        location, meeting_start, meeting_end, travel_time = result
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': friend_name,
            'start_time': format_time(minutes_to_time(meeting_start)),
            'end_time': format_time(minutes_to_time(meeting_end))
        })
        scheduled_friends.add(friend_name)
        current_location = location
        current_time = meeting_end
    
    return itinerary, len(scheduled_friends)

def find_best_schedule():
    best_schedule = None
    best_count = 0
    
    # Try different orders prioritizing friends with tighter time windows
    priority_order = [
        'Joseph', 'Elizabeth', 'Sandra', 'Carol', 'William', 
        'Anthony', 'Stephanie', 'Barbara', 'Kenneth'
    ]
    
    # Try permutations of priority order
    for perm in permutations(priority_order[:5], 5):
        order = list(perm) + priority_order[5:]
        itinerary, count = evaluate_schedule(order)
        if count > best_count or (count == best_count and len(itinerary) > len(best_schedule)):
            best_schedule = itinerary
            best_count = count
    
    return best_schedule

best_itinerary = find_best_schedule()
output = {"itinerary": best_itinerary}
print(json.dumps(output, indent=2))