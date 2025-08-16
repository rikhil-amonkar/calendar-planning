import itertools
from z3 import *
import json

def solve():
    friends = [
        {
            'name': 'Daniel',
            'location': 'Golden Gate Park',
            'available_start': 8 * 60,  # 8:00 AM
            'available_end': 13 * 60 + 30,  # 1:30 PM
            'min_duration': 15
        },
        {
            'name': 'Margaret',
            'location': 'Russian Hill',
            'available_start': 9 * 60,  # 9:00 AM
            'available_end': 16 * 60,  # 4:00 PM
            'min_duration': 30
        },
        {
            'name': 'Charles',
            'location': 'Alamo Square',
            'available_start': 18 * 60,  # 6:00 PM
            'available_end': 20 * 60 + 45,  # 8:45 PM
            'min_duration': 90
        },
        {
            'name': 'Stephanie',
            'location': 'Mission District',
            'available_start': 20 * 60 + 30,  # 8:30 PM
            'available_end': 22 * 60,  # 10:00 PM
            'min_duration': 90
        }
    ]

    travel_times = {
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Mission District'): 24,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Mission District'): 10,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Mission District'): 16,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Alamo Square'): 11,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Golden Gate Park'): 17,
    }

    for subset_size in range(4, 0, -1):
        for subset in itertools.combinations(friends, subset_size):
            for perm in itertools.permutations(subset):
                s = Solver()
                start_vars = {}
                for friend in perm:
                    start_vars[friend['name']] = Int(f"start_{friend['name']}")
                prev_loc = 'Sunset District'
                prev_end = 9 * 60  # 9:00 AM
                constraints = []
                for friend in perm:
                    travel_time = travel_times[(prev_loc, friend['location'])]
                    arrival_time = prev_end + travel_time
                    available_start = friend['available_start']
                    available_end = friend['available_end']
                    min_duration = friend['min_duration']
                    start = start_vars[friend['name']]
                    constraints.append(start >= max(arrival_time, available_start))
                    constraints.append(start + min_duration <= available_end)
                    prev_end = start + min_duration
                    prev_loc = friend['location']
                s.add(And(constraints))
                if s.check() == sat:
                    model = s.model()
                    itinerary = []
                    prev_loc = 'Sunset District'
                    prev_end = 9 * 60
                    for friend in perm:
                        travel_time = travel_times[(prev_loc, friend['location'])]
                        arrival_time = prev_end + travel_time
                        start_val = model.evaluate(start_vars[friend['name']]).as_long()
                        end_val = start_val + friend['min_duration']
                        start_hh = start_val // 60
                        start_mm = start_val % 60
                        end_hh = end_val // 60
                        end_mm = end_val % 60
                        start_str = f"{start_hh:02d}:{start_mm:02d}"
                        end_str = f"{end_hh:02d}:{end_mm:02d}"
                        itinerary.append({
                            "action": "meet",
                            "person": friend['name'],
                            "start_time": start_str,
                            "end_time": end_str
                        })
                        prev_end = end_val
                        prev_loc = friend['location']
                    return {"itinerary": itinerary}
    return {"itinerary": []}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))