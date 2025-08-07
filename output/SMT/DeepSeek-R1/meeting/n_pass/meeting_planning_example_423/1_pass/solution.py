import itertools
import json

def main():
    # Travel time matrix
    travel = {
        'Presidio': {
            'Richmond District': 7,
            'North Beach': 18,
            'Financial District': 23,
            'Golden Gate Park': 12,
            'Union Square': 22
        },
        'Richmond District': {
            'Presidio': 7,
            'North Beach': 17,
            'Financial District': 22,
            'Golden Gate Park': 9,
            'Union Square': 21
        },
        'North Beach': {
            'Presidio': 17,
            'Richmond District': 18,
            'Financial District': 8,
            'Golden Gate Park': 22,
            'Union Square': 7
        },
        'Financial District': {
            'Presidio': 22,
            'Richmond District': 21,
            'North Beach': 7,
            'Golden Gate Park': 23,
            'Union Square': 9
        },
        'Golden Gate Park': {
            'Presidio': 11,
            'Richmond District': 7,
            'North Beach': 24,
            'Financial District': 26,
            'Union Square': 22
        },
        'Union Square': {
            'Presidio': 24,
            'Richmond District': 20,
            'North Beach': 10,
            'Financial District': 9,
            'Golden Gate Park': 22
        }
    }
    
    friends = ['Jason', 'Melissa', 'Brian', 'Elizabeth', 'Laura']
    locations_map = {
        'Jason': 'Richmond District',
        'Melissa': 'North Beach',
        'Brian': 'Financial District',
        'Elizabeth': 'Golden Gate Park',
        'Laura': 'Union Square'
    }
    
    min_times = {
        'Jason': 90,
        'Melissa': 45,
        'Brian': 15,
        'Elizabeth': 105,
        'Laura': 75
    }
    
    # Convert availability times to minutes from 9:00 AM
    available_start = {
        'Jason': (13 * 60) - (9 * 60),      # 13:00 -> 240 minutes
        'Melissa': (18 * 60 + 45) - (9 * 60), # 18:45 -> 585 minutes
        'Brian': (9 * 60 + 45) - (9 * 60),    # 9:45 -> 45 minutes
        'Elizabeth': 0,                       # 8:45 AM, but we start at 9:00 -> 0 minutes
        'Laura': (14 * 60 + 15) - (9 * 60)    # 14:15 -> 315 minutes
    }
    
    available_end = {
        'Jason': (20 * 60 + 45) - (9 * 60),   # 20:45 -> 705 minutes
        'Melissa': (20 * 60 + 15) - (9 * 60),  # 20:15 -> 675 minutes
        'Brian': (21 * 60 + 45) - (9 * 60),    # 21:45 -> 765 minutes
        'Elizabeth': (21 * 60 + 30) - (9 * 60), # 21:30 -> 750 minutes
        'Laura': (19 * 60 + 30) - (9 * 60)     # 19:30 -> 630 minutes
    }
    
    # Generate all subsets of friends
    all_subsets = []
    for r in range(1, len(friends) + 1):
        all_subsets.extend(itertools.combinations(friends, r))
    
    best_count = 0
    best_schedule = None
    
    for subset in all_subsets:
        for perm in itertools.permutations(subset):
            current_loc = 'Presidio'
            current_time = 0.0
            schedule = []
            valid = True
            
            for friend in perm:
                loc = locations_map[friend]
                tt = travel[current_loc][loc]
                current_time += tt
                start_time = max(current_time, available_start[friend])
                end_time = start_time + min_times[friend]
                if end_time > available_end[friend]:
                    valid = False
                    break
                schedule.append((friend, start_time, end_time))
                current_time = end_time
                current_loc = loc
            
            if valid and len(subset) > best_count:
                best_count = len(subset)
                best_schedule = schedule
                # Since we found a schedule with 5 friends, we can break early
                if best_count == 5:
                    break
        if best_count == 5:
            break
    
    if best_schedule is None:
        print('{"itinerary": []}')
        return
    
    def format_time(minutes):
        total_minutes = 9 * 60 + minutes
        hours = total_minutes // 60
        mins = total_minutes % 60
        return f"{int(hours):02d}:{int(mins):02d}"
    
    itinerary = []
    for (friend, start, end) in best_schedule:
        itinerary.append({
            "action": "meet",
            "person": friend,
            "start_time": format_time(start),
            "end_time": format_time(end)
        })
    
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result))

if __name__ == '__main__':
    main()