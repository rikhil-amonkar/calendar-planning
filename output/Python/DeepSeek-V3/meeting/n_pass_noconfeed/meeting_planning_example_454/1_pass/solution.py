import json
from itertools import permutations

# Travel times in minutes between locations
travel_times = {
    'Presidio': {
        'Golden Gate Park': 12,
        'Bayview': 31,
        'Chinatown': 21,
        'North Beach': 18,
        'Mission District': 26
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Bayview': 23,
        'Chinatown': 23,
        'North Beach': 24,
        'Mission District': 17
    },
    'Bayview': {
        'Presidio': 31,
        'Golden Gate Park': 22,
        'Chinatown': 18,
        'North Beach': 21,
        'Mission District': 13
    },
    'Chinatown': {
        'Presidio': 19,
        'Golden Gate Park': 23,
        'Bayview': 22,
        'North Beach': 3,
        'Mission District': 18
    },
    'North Beach': {
        'Presidio': 17,
        'Golden Gate Park': 22,
        'Bayview': 22,
        'Chinatown': 6,
        'Mission District': 18
    },
    'Mission District': {
        'Presidio': 25,
        'Golden Gate Park': 17,
        'Bayview': 15,
        'Chinatown': 16,
        'North Beach': 17
    }
}

# Friend constraints
friends = {
    'Jessica': {
        'location': 'Golden Gate Park',
        'start': '13:45',
        'end': '15:00',
        'min_duration': 30
    },
    'Ashley': {
        'location': 'Bayview',
        'start': '17:15',
        'end': '20:00',
        'min_duration': 105
    },
    'Ronald': {
        'location': 'Chinatown',
        'start': '7:15',
        'end': '14:45',
        'min_duration': 90
    },
    'William': {
        'location': 'North Beach',
        'start': '13:15',
        'end': '20:15',
        'min_duration': 15
    },
    'Daniel': {
        'location': 'Mission District',
        'start': '7:00',
        'end': '11:15',
        'min_duration': 105
    }
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_available_slots(person, current_time):
    friend = friends[person]
    start = time_to_minutes(friend['start'])
    end = time_to_minutes(friend['end'])
    min_duration = friend['min_duration']
    
    if current_time >= end:
        return []
    
    available_start = max(current_time, start)
    available_end = end
    
    if available_end - available_start < min_duration:
        return []
    
    return [(available_start, available_end)]

def calculate_schedule_quality(schedule):
    total_meetings = len(schedule)
    total_duration = sum(meet['duration'] for meet in schedule)
    return (total_meetings, total_duration)

def generate_schedules(current_location, current_time, remaining_friends, path):
    if not remaining_friends:
        return [path]
    
    schedules = []
    for friend in remaining_friends:
        location = friends[friend]['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        slots = get_available_slots(friend, arrival_time)
        for slot_start, slot_end in slots:
            min_duration = friends[friend]['min_duration']
            meet_duration = min(min_duration, slot_end - slot_start)
            meet_end = slot_start + meet_duration
            
            new_path = path + [{
                'action': 'meet',
                'location': location,
                'person': friend,
                'start_time': minutes_to_time(slot_start),
                'end_time': minutes_to_time(meet_end),
                'duration': meet_duration
            }]
            
            new_remaining = [f for f in remaining_friends if f != friend]
            schedules += generate_schedules(location, meet_end, new_remaining, new_path)
    
    return schedules

def find_best_schedule():
    initial_location = 'Presidio'
    initial_time = time_to_minutes('9:00')
    all_friends = list(friends.keys())
    
    all_schedules = generate_schedules(initial_location, initial_time, all_friends, [])
    
    if not all_schedules:
        return {"itinerary": []}
    
    best_schedule = max(all_schedules, key=calculate_schedule_quality)
    
    # Convert to required output format
    itinerary = []
    for meet in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meet["location"],
            "person": meet["person"],
            "start_time": meet["start_time"],
            "end_time": meet["end_time"]
        })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    best_schedule = find_best_schedule()
    print(json.dumps(best_schedule, indent=2))