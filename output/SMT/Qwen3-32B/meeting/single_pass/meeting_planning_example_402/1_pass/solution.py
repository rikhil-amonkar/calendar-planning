import itertools
import json
from z3 import *

# Define friends' data
friends_data = {
    'Matthew': {
        'location': 'Marina District',
        'available_start': 9 * 60 + 15,  # 555
        'available_end': 12 * 60,        # 720
        'duration': 15,
    },
    'Robert': {
        'location': 'Union Square',
        'available_start': 10 * 60 + 15,  # 615
        'available_end': 21 * 60 + 45,    # 21:45 = 1305
        'duration': 15,
    },
    'Joseph': {
        'location': 'Financial District',
        'available_start': 14 * 60 + 15,  # 855
        'available_end': 18 * 60 + 45,    # 1065
        'duration': 30,
    },
    'Sarah': {
        'location': 'Haight-Ashbury',
        'available_start': 17 * 60,       # 1020
        'available_end': 21 * 60 + 30,    # 1290
        'duration': 105,
    },
    'Patricia': {
        'location': 'Sunset District',
        'available_start': 17 * 60,       # 1020
        'available_end': 19 * 60 + 45,    # 1185
        'duration': 45,
    },
}

# Define travel times
travel_times = {
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Union Square'): 30,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Union Square'): 16,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Union Square'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Financial District'): 9,
}

def get_travel_time(from_loc, to_loc):
    return travel_times[(from_loc, to_loc)]

def find_feasible_sequence():
    friends_list = ['Matthew', 'Robert', 'Joseph', 'Sarah', 'Patricia']
    for subset_size in range(len(friends_list), 0, -1):
        for subset in itertools.combinations(friends_list, subset_size):
            for perm in itertools.permutations(subset):
                s = Solver()
                current_time = 540  # 9:00 AM in minutes
                current_location = 'Golden Gate Park'
                start_vars = {}
                end_vars = {}
                for i, friend in enumerate(perm):
                    data = friends_data[friend]
                    loc = data['location']
                    available_start = data['available_start']
                    available_end = data['available_end']
                    duration = data['duration']
                    start = Int(f"{friend}_start")
                    end = Int(f"{friend}_end")
                    start_vars[friend] = start
                    end_vars[friend] = end
                    travel_time = get_travel_time(current_location, loc)
                    arrival_time = current_time + travel_time
                    s.add(start >= arrival_time)
                    s.add(start >= available_start)
                    s.add(end == start + duration)
                    s.add(end <= available_end)
                    current_time = end
                    current_location = loc
                if s.check() == sat:
                    model = s.model()
                    itinerary = []
                    current_time = 540
                    current_location = 'Golden Gate Park'
                    for friend in perm:
                        data = friends_data[friend]
                        loc = data['location']
                        travel_time = get_travel_time(current_location, loc)
                        arrival_time = current_time + travel_time
                        start = model.evaluate(start_vars[friend])
                        end = model.evaluate(end_vars[friend])
                        # Convert to HH:MM
                        start_hh = start // 60
                        start_mm = start % 60
                        end_hh = end // 60
                        end_mm = end % 60
                        start_time = f"{start_hh:02d}:{start_mm:02d}"
                        end_time = f"{end_hh:02d}:{end_mm:02d}"
                        itinerary.append({
                            "action": "meet",
                            "person": friend,
                            "start_time": start_time,
                            "end_time": end_time
                        })
                        current_time = end
                        current_location = loc
                    return itinerary
    return None

itinerary = find_feasible_sequence()
if itinerary:
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No feasible itinerary found.")