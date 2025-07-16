import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

travel_times = {
    'Pacific Heights': {'Pacific Heights': 0, 'Marina': 10, 'Richmond': 20, 'Sunset': 20, 'SOMA': 15, 'Mission': 20, 'Nob Hill': 10},
    'Marina': {'Pacific Heights': 10, 'Marina': 0, 'Richmond': 15, 'Sunset': 25, 'SOMA': 20, 'Mission': 25, 'Nob Hill': 10},
    'Richmond': {'Pacific Heights': 20, 'Marina': 15, 'Richmond': 0, 'Sunset': 10, 'SOMA': 25, 'Mission': 30, 'Nob Hill': 15},
    'Sunset': {'Pacific Heights': 20, 'Marina': 25, 'Richmond': 10, 'Sunset': 0, 'SOMA': 20, 'Mission': 25, 'Nob Hill': 15},
    'SOMA': {'Pacific Heights': 15, 'Marina': 20, 'Richmond': 25, 'Sunset': 20, 'SOMA': 0, 'Mission': 5, 'Nob Hill': 10},
    'Mission': {'Pacific Heights': 20, 'Marina': 25, 'Richmond': 30, 'Sunset': 25, 'SOMA': 5, 'Mission': 0, 'Nob Hill': 15},
    'Nob Hill': {'Pacific Heights': 10, 'Marina': 10, 'Richmond': 15, 'Sunset': 15, 'SOMA': 10, 'Mission': 15, 'Nob Hill': 0}
}

friends = [
    {'name': 'Alice', 'location': 'Marina', 'available_start': '9:30', 'available_end': '10:30', 'min_duration': 30},
    {'name': 'Bob', 'location': 'Mission', 'available_start': '12:00', 'available_end': '13:00', 'min_duration': 30},
    {'name': 'Charlie', 'location': 'SOMA', 'available_start': '11:00', 'available_end': '12:30', 'min_duration': 15},
    {'name': 'Dana', 'location': 'Richmond', 'available_start': '10:00', 'available_end': '11:30', 'min_duration': 20},
    {'name': 'Eve', 'location': 'Nob Hill', 'available_start': '9:00', 'available_end': '10:00', 'min_duration': 15}
]

def find_best_schedule():
    current_location = 'Pacific Heights'
    current_time = time_to_minutes('9:00')
    
    best_schedule = []
    max_friends = 0
    min_total_time = float('inf')
    
    # Try all possible permutations of friends to find optimal order
    for friend_order in permutations(friends):
        schedule = []
        valid = True
        loc = current_location
        time = current_time
        
        for friend in friend_order:
            travel = travel_times[loc][friend['location']]
            arrival = time + travel
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])
            
            start = max(arrival, available_start)
            end = start + friend['min_duration']
            
            if end > available_end:
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
        
        if valid:
            # Prefer schedules that meet more friends
            if len(schedule) > max_friends:
                best_schedule = schedule
                max_friends = len(schedule)
                min_total_time = time - current_time
            # If same number of friends, choose the one that finishes earliest
            elif len(schedule) == max_friends and (time - current_time) < min_total_time:
                best_schedule = schedule
                min_total_time = time - current_time
    
    return best_schedule

def main():
    best_schedule = find_best_schedule()
    print(json.dumps({"itinerary": best_schedule}, indent=2))

if __name__ == "__main__":
    main()