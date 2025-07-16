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
    min_end_time = float('inf')
    
    def backtrack(remaining_friends, current_schedule, current_loc, current_time):
        nonlocal best_schedule, max_friends, min_end_time
        
        # Try all remaining friends
        for i, friend in enumerate(remaining_friends):
            travel = travel_times[current_loc][friend['location']]
            arrival = current_time + travel
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])
            
            # Calculate possible meeting window
            start = max(arrival, available_start)
            end = start + friend['min_duration']
            
            # Check if meeting is possible
            if end <= available_end:
                new_schedule = current_schedule.copy()
                new_schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(start),
                    'end_time': minutes_to_time(end)
                })
                
                new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
                backtrack(new_remaining, new_schedule, friend['location'], end)
        
        # Update best schedule if current one is better
        if len(current_schedule) > max_friends or \
           (len(current_schedule) == max_friends and (current_time < min_end_time or len(current_schedule) == 0)):
            best_schedule = current_schedule
            max_friends = len(current_schedule)
            min_end_time = current_time
    
    # Start with all friends
    backtrack(friends, [], current_location, current_time)
    return best_schedule

def main():
    best_schedule = find_best_schedule()
    print(json.dumps({"itinerary": best_schedule}, indent=2))

if __name__ == "__main__":
    main()