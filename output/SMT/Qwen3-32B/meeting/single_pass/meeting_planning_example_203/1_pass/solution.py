import itertools
from z3 import *

def solve():
    friends = ['Timothy', 'David', 'Robert']
    friends_data = {
        'Timothy': {
            'location': 'Pacific Heights',
            'available_start': 540,  # 9:00 AM
            'available_end': 930,    # 3:30 PM
            'duration': 75
        },
        'David': {
            'location': "Fisherman's Wharf",
            'available_start': 645,  # 10:45 AM
            'available_end': 930,    # 3:30 PM
            'duration': 15
        },
        'Robert': {
            'location': 'Mission District',
            'available_start': 735,  # 12:15 PM
            'available_end': 1185,   # 7:45 PM
            'duration': 90
        }
    }
    travel_times = {
        ('Financial District', "Fisherman's Wharf"): 10,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Mission District'): 17,
        ("Fisherman's Wharf", 'Financial District'): 11,
        ("Fisherman's Wharf", 'Pacific Heights'): 12,
        ("Fisherman's Wharf", 'Mission District'): 22,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', "Fisherman's Wharf"): 13,
        ('Pacific Heights', 'Mission District'): 15,
        ('Mission District', 'Financial District'): 17,
        ('Mission District', "Fisherman's Wharf"): 22,
        ('Mission District', 'Pacific Heights'): 16,
    }

    for length in range(3, 0, -1):
        for perm in itertools.permutations(friends, length):
            s = Solver()
            start_times = {}
            end_times = {}
            prev_end_time = 540  # Start at 9:00 AM
            prev_location = 'Financial District'
            for friend in perm:
                loc = friends_data[friend]['location']
                travel_time = travel_times[(prev_location, loc)]
                arrival_time = prev_end_time + travel_time
                available_start = friends_data[friend]['available_start']
                available_end = friends_data[friend]['available_end']
                duration = friends_data[friend]['duration']
                st = Int(f"{friend}_start")
                et = Int(f"{friend}_end")
                s.add(st >= arrival_time)
                s.add(st >= available_start)
                s.add(et == st + duration)
                s.add(et <= available_end)
                start_times[friend] = st
                end_times[friend] = et
                prev_end_time = et
                prev_location = loc
            if s.check() == sat:
                model = s.model()
                itinerary = []
                for friend in perm:
                    st_val = model[start_times[friend]].as_long()
                    et_val = model[end_times[friend]].as_long()
                    h1 = st_val // 60
                    m1 = st_val % 60
                    start_time = f"{h1:02d}:{m1:02d}"
                    h2 = et_val // 60
                    m2 = et_val % 60
                    end_time = f"{h2:02d}:{m2:02d}"
                    itinerary.append({
                        "action": "meet",
                        "person": friend,
                        "start_time": start_time,
                        "end_time": end_time
                    })
                return {"itinerary": itinerary}
    return {"itinerary": []}

solution = solve()
print(solution)