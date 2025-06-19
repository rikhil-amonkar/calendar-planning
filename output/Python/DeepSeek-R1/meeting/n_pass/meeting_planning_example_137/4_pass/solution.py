import json
from itertools import permutations

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        'Financial District': {'Chinatown': 5, 'Golden Gate Park': 23},
        'Chinatown': {'Financial District': 5, 'Golden Gate Park': 23},
        'Golden Gate Park': {'Financial District': 23, 'Chinatown': 23}
    }
    
    friends = {
        'Barbara': {
            'location': 'Golden Gate Park',
            'available_start': 8*60 + 15,  # 8:15
            'available_end': 19*60,        # 19:00
            'min_duration': 45
        },
        'Kenneth': {
            'location': 'Chinatown',
            'available_start': 12*60,      # 12:00
            'available_end': 15*60,         # 15:00
            'min_duration': 90
        }
    }
    
    start_location = 'Financial District'
    start_time = 9*60  # 9:00
    candidates = []
    friend_names = list(friends.keys())
    
    # Try all permutations of friends
    for perm in permutations(friend_names):
        current_loc = start_location
        current_time = start_time
        schedule = []
        first_start_min = None
        last_end_min = None
        
        for friend in perm:
            loc = friends[friend]['location']
            avail_start = friends[friend]['available_start']
            avail_end = friends[friend]['available_end']
            min_dur = friends[friend]['min_duration']
            
            # Travel to friend's location
            travel_time = travel_times[current_loc][loc]
            current_time += travel_time
            
            # Calculate meeting times
            start_meeting = max(current_time, avail_start)
            end_meeting = start_meeting + min_dur
            
            # Check if meeting fits in friend's availability
            if end_meeting > avail_end:
                # Revert travel time (skip this friend)
                current_time -= travel_time
                continue
                
            # Record first meeting start time
            if first_start_min is None:
                first_start_min = start_meeting
            last_end_min = end_meeting
            
            # Add meeting to schedule
            schedule.append({
                'action': 'meet',
                'location': loc,
                'person': friend,
                'start_time': format_time(start_meeting),
                'end_time': format_time(end_meeting)
            })
            
            # Update location and time after meeting
            current_loc = loc
            current_time = end_meeting
        
        # If we have at least one meeting, add to candidates
        if schedule:
            total_duration = last_end_min - first_start_min
            candidates.append((len(schedule), total_duration, schedule))
    
    # Select best candidate: most friends then shortest duration
    if candidates:
        candidates.sort(key=lambda x: (-x[0], x[1]))
        best_schedule = candidates[0][2]
    else:
        best_schedule = []
    
    print(json.dumps({"itinerary": best_schedule}))

if __name__ == "__main__":
    main()