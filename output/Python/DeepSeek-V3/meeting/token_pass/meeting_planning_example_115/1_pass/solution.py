import json

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Travel times in minutes: from -> to
    travel = {
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Marina District'): 9,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'Marina District'): 6,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Pacific Heights'): 7,
    }
    
    # Start
    start_loc = 'Richmond District'
    start_time = time_to_minutes('9:00')
    
    # Friend data: location, window_start, window_end, min_duration
    friends = [
        {'name': 'Carol', 'loc': 'Marina District', 
         'start': time_to_minutes('11:30'), 'end': time_to_minutes('15:00'), 'dur': 60},
        {'name': 'Jessica', 'loc': 'Pacific Heights', 
         'start': time_to_minutes('15:30'), 'end': time_to_minutes('16:45'), 'dur': 45},
    ]
    
    # Try all permutations of meeting order
    from itertools import permutations
    best_schedule = None
    best_met = 0
    
    for perm in permutations(friends):
        current_loc = start_loc
        current_time = start_time
        schedule = []
        met_count = 0
        
        for f in perm:
            # Travel to friend's location
            travel_time = travel.get((current_loc, f['loc']))
            if travel_time is None:
                # Should not happen given complete travel matrix
                travel_time = 0
            arrival = current_time + travel_time
            
            # Start meeting as soon as possible within window
            meet_start = max(arrival, f['start'])
            if meet_start + f['dur'] <= f['end']:
                # Can meet
                meet_end = meet_start + f['dur']
                schedule.append({
                    'action': 'meet',
                    'location': f['loc'],
                    'person': f['name'],
                    'start_time': minutes_to_time(meet_start),
                    'end_time': minutes_to_time(meet_end)
                })
                met_count += 1
                current_time = meet_end
                current_loc = f['loc']
            else:
                # Cannot meet this friend in this order
                break
        
        if met_count > best_met:
            best_met = met_count
            best_schedule = schedule
    
    # Output
    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()