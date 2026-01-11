import itertools
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

# Travel times in minutes between locations
travel_times = {
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Bayview'): 26,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Bayview'): 15,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Mission District'): 13,
}

# Friends data: name, location, start, end, min_duration
friends = [
    ('Sarah', 'Fisherman\'s Wharf', time_to_minutes('14:45'), time_to_minutes('17:30'), 105),
    ('Mary', 'Richmond District', time_to_minutes('13:00'), time_to_minutes('19:15'), 75),
    ('Helen', 'Mission District', time_to_minutes('21:45'), time_to_minutes('22:30'), 30),
    ('Thomas', 'Bayview', time_to_minutes('15:15'), time_to_minutes('18:45'), 120),
]

def can_schedule(order):
    """Check if a given order of friends is feasible, return total meeting minutes and itinerary."""
    current_location = 'Haight-Ashbury'
    current_time = time_to_minutes('9:00')
    total_meeting_time = 0
    itinerary = []
    
    for name, location, start, end, min_dur in order:
        # Travel to friend's location
        travel = travel_times.get((current_location, location))
        if travel is None:
            travel = travel_times.get((location, current_location))  # symmetric fallback
        arrive = current_time + travel
        
        # If we arrive before friend's start, wait
        if arrive < start:
            arrive = start
        
        # If we arrive after friend's end, impossible
        if arrive >= end:
            return -1, []
        
        # Calculate possible meeting end time
        meeting_end = min(arrive + min_dur, end)
        if meeting_end - arrive < min_dur:
            return -1, []  # can't meet minimum
        
        # Add meeting to itinerary
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': name,
            'start_time': minutes_to_time(arrive),
            'end_time': minutes_to_time(meeting_end)
        })
        
        total_meeting_time += meeting_end - arrive
        current_location = location
        current_time = meeting_end
    
    return total_meeting_time, itinerary

def main():
    best_total = -1
    best_itinerary = []
    
    # Try all permutations of subsets of friends (size 1 to 4)
    for r in range(1, len(friends) + 1):
        for perm in itertools.permutations(friends, r):
            total, itinerary = can_schedule(perm)
            if total > best_total:
                best_total = total
                best_itinerary = itinerary
    
    # Output as JSON
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()