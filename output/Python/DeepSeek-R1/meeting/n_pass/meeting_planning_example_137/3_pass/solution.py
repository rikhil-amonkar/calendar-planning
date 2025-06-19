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
            'available_start': 8*60 + 15,
            'available_end': 19*60,
            'min_duration': 45
        },
        'Kenneth': {
            'location': 'Chinatown',
            'available_start': 12*60,
            'available_end': 15*60,
            'min_duration': 90
        }
    }
    
    start_location = 'Financial District'
    start_time = 9*60
    candidates = []
    friend_names = list(friends.keys())
    
    for perm in permutations(friend_names):
        current_loc = start_location
        current_time = start_time
        schedule = []
        feasible = True
        
        for friend in perm:
            loc = friends[friend]['location']
            avail_start = friends[friend]['available_start']
            avail_end = friends[friend]['available_end']
            min_dur = friends[friend]['min_duration']
            
            # Travel to friend
            current_time += travel_times[current_loc][loc]
            start_meeting = max(current_time, avail_start)
            end_meeting = start_meeting + min_dur
            
            # Check availability
            if end_meeting > avail_end:
                feasible = False
                break
                
            schedule.append({
                'action': 'meet',
                'location': loc,
                'person': friend,
                'start_time': format_time(start_meeting),
                'end_time': format_time(end_meeting)
            })
            
            current_loc = loc
            current_time = end_meeting
        
        if feasible:
            candidates.append((len(perm), current_time, schedule))
    
    # Try single friend if no two-friend schedules
    if not candidates:
        for friend in friend_names:
            current_loc = start_location
            current_time = start_time
            schedule = []
            
            loc = friends[friend]['location']
            avail_start = friends[friend]['available_start']
            avail_end = friends[friend]['available_end']
            min_dur = friends[friend]['min_duration']
            
            current_time += travel_times[current_loc][loc]
            start_meeting = max(current_time, avail_start)
            end_meeting = start_meeting + min_dur
            
            if end_meeting > avail_end:
                continue
                
            schedule.append({
                'action': 'meet',
                'location': loc,
                'person': friend,
                'start_time': format_time(start_meeting),
                'end_time': format_time(end_meeting)
            })
            candidates.append((1, end_meeting, schedule))
    
    # Select best candidate
    if candidates:
        candidates.sort(key=lambda x: (-x[0], x[1]))
        best_schedule = candidates[0][2]
    else:
        best_schedule = []
    
    print(json.dumps({"itinerary": best_schedule}))

if __name__ == "__main__":
    main()