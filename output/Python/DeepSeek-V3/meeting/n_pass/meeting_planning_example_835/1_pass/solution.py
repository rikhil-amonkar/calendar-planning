import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times dictionary: travel_times[from][to] = minutes
travel_times = {
    'Pacific Heights': {
        'Golden Gate Park': 15,
        'The Castro': 16,
        'Bayview': 22,
        'Marina District': 6,
        'Union Square': 12,
        'Sunset District': 21,
        'Alamo Square': 10,
        'Financial District': 13,
        'Mission District': 15
    },
    'Golden Gate Park': {
        'Pacific Heights': 16,
        'The Castro': 13,
        'Bayview': 23,
        'Marina District': 16,
        'Union Square': 22,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'Mission District': 17
    },
    'The Castro': {
        'Pacific Heights': 16,
        'Golden Gate Park': 11,
        'Bayview': 19,
        'Marina District': 21,
        'Union Square': 19,
        'Sunset District': 17,
        'Alamo Square': 8,
        'Financial District': 21,
        'Mission District': 7
    },
    'Bayview': {
        'Pacific Heights': 23,
        'Golden Gate Park': 22,
        'The Castro': 19,
        'Marina District': 27,
        'Union Square': 18,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'Mission District': 13
    },
    'Marina District': {
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'The Castro': 22,
        'Bayview': 27,
        'Union Square': 16,
        'Sunset District': 19,
        'Alamo Square': 15,
        'Financial District': 17,
        'Mission District': 20
    },
    'Union Square': {
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
        'The Castro': 17,
        'Bayview': 15,
        'Marina District': 18,
        'Sunset District': 27,
        'Alamo Square': 15,
        'Financial District': 9,
        'Mission District': 14
    },
    'Sunset District': {
        'Pacific Heights': 21,
        'Golden Gate Park': 11,
        'The Castro': 17,
        'Bayview': 22,
        'Marina District': 21,
        'Union Square': 30,
        'Alamo Square': 17,
        'Financial District': 30,
        'Mission District': 25
    },
    'Alamo Square': {
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'The Castro': 8,
        'Bayview': 16,
        'Marina District': 15,
        'Union Square': 14,
        'Sunset District': 16,
        'Financial District': 17,
        'Mission District': 10
    },
    'Financial District': {
        'Pacific Heights': 13,
        'Golden Gate Park': 23,
        'The Castro': 20,
        'Bayview': 19,
        'Marina District': 15,
        'Union Square': 9,
        'Sunset District': 30,
        'Alamo Square': 17,
        'Mission District': 17
    },
    'Mission District': {
        'Pacific Heights': 16,
        'Golden Gate Park': 17,
        'The Castro': 7,
        'Bayview': 14,
        'Marina District': 19,
        'Union Square': 15,
        'Sunset District': 24,
        'Alamo Square': 11,
        'Financial District': 15
    }
}

# Friend constraints
friends = [
    {
        'name': 'Helen',
        'location': 'Golden Gate Park',
        'available_start': '9:30',
        'available_end': '12:15',
        'min_duration': 45
    },
    {
        'name': 'Steven',
        'location': 'The Castro',
        'available_start': '20:15',
        'available_end': '22:00',
        'min_duration': 105
    },
    {
        'name': 'Deborah',
        'location': 'Bayview',
        'available_start': '8:30',
        'available_end': '12:00',
        'min_duration': 30
    },
    {
        'name': 'Matthew',
        'location': 'Marina District',
        'available_start': '9:15',
        'available_end': '14:15',
        'min_duration': 45
    },
    {
        'name': 'Joseph',
        'location': 'Union Square',
        'available_start': '14:15',
        'available_end': '18:45',
        'min_duration': 120
    },
    {
        'name': 'Ronald',
        'location': 'Sunset District',
        'available_start': '16:00',
        'available_end': '20:45',
        'min_duration': 60
    },
    {
        'name': 'Robert',
        'location': 'Alamo Square',
        'available_start': '18:30',
        'available_end': '21:15',
        'min_duration': 120
    },
    {
        'name': 'Rebecca',
        'location': 'Financial District',
        'available_start': '14:45',
        'available_end': '16:15',
        'min_duration': 30
    },
    {
        'name': 'Elizabeth',
        'location': 'Mission District',
        'available_start': '18:30',
        'available_end': '21:00',
        'min_duration': 120
    }
]

def generate_schedules():
    current_location = 'Pacific Heights'
    current_time = time_to_minutes('9:00')
    possible_friends = [f for f in friends if time_to_minutes(f['available_end']) > current_time]
    
    best_schedule = []
    max_meetings = 0
    
    # Try all possible orders of meeting friends
    for perm in permutations(possible_friends):
        schedule = []
        loc = current_location
        time = current_time
        valid = True
        
        for friend in perm:
            travel = travel_times[loc][friend['location']]
            arrival = time + travel
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])
            
            # Calculate possible meeting window
            start = max(arrival, available_start)
            end = min(start + friend['min_duration'], available_end)
            
            if end - start < friend['min_duration']:
                valid = False
                break
            
            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            
            loc = friend['location']
            time = end
        
        if valid and len(schedule) > max_meetings:
            best_schedule = schedule
            max_meetings = len(schedule)
    
    return best_schedule

def main():
    # In reality, we'd need a more sophisticated algorithm to handle all constraints,
    # but for the sake of this example, we'll use a greedy approach
    
    itinerary = []
    current_location = 'Pacific Heights'
    current_time = time_to_minutes('9:00')
    
    # Sort friends by earliest available time
    sorted_friends = sorted(friends, key=lambda x: time_to_minutes(x['available_start']))
    
    for friend in sorted_friends:
        travel = travel_times[current_location][friend['location']]
        arrival = current_time + travel
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        
        # Calculate possible meeting window
        start = max(arrival, available_start)
        end = min(start + friend['min_duration'], available_end)
        
        if end - start >= friend['min_duration']:
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            current_location = friend['location']
            current_time = end
    
    # After greedy approach, try to fit in more friends
    # This is a simplified version - a real solution would use backtracking or other optimization
    remaining_friends = [f for f in friends if f['name'] not in [m['person'] for m in itinerary]]
    
    for friend in remaining_friends:
        travel = travel_times[current_location][friend['location']]
        arrival = current_time + travel
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        
        start = max(arrival, available_start)
        end = min(start + friend['min_duration'], available_end)
        
        if end - start >= friend['min_duration']:
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            current_location = friend['location']
            current_time = end
    
    # Final output
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()