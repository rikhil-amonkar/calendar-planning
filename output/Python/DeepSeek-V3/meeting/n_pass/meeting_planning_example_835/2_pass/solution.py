import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Travel times dictionary remains the same
travel_times = {
    # ... (same travel_times dictionary as before)
}

# Friend constraints remain the same
friends = [
    # ... (same friends list as before)
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
            end = min(start + friend['min_duration'], available_end)
            
            # Check if meeting is possible
            if end - start >= friend['min_duration']:
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
           (len(current_schedule) == max_friends and current_time < min_end_time):
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