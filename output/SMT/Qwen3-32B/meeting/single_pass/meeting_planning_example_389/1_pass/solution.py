from z3 import *
import itertools
import json

friends_info = {
    'Mary': {
        'location': 'Richmond District',
        'available_start': 780,  # 13:00
        'available_end': 1155,   # 19:15
        'required_duration': 75,
    },
    'Sarah': {
        'location': 'Fisherman\'s Wharf',
        'available_start': 885,  # 14:45
        'available_end': 1050,   # 17:30
        'required_duration': 105,
    },
    'Thomas': {
        'location': 'Bayview',
        'available_start': 915,  # 15:15
        'available_end': 1125,   # 18:45
        'required_duration': 120,
    },
    'Helen': {
        'location': 'Mission District',
        'available_start': 1305, # 21:45
        'available_end': 1335,   # 22:15
        'required_duration': 30,
    },
}

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

def get_travel_time(from_loc, to_loc):
    return travel_times[(from_loc, to_loc)]

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    for subset in itertools.combinations(friends_info.keys(), 3):
        for perm in itertools.permutations(subset):
            s = Solver()
            start_times = {}
            for friend in perm:
                start_times[friend] = Int(f"start_{friend}")
            current_loc = 'Haight-Ashbury'
            current_time = 540  # 9:00 AM
            for friend in perm:
                info = friends_info[friend]
                loc = info['location']
                avail_start = info['available_start']
                avail_end = info['available_end']
                duration = info['required_duration']
                travel_time = get_travel_time(current_loc, loc)
                arrival_time = current_time + travel_time
                start = start_times[friend]
                end = start + duration
                s.add(start >= arrival_time)
                s.add(start >= avail_start)
                s.add(end <= avail_end)
                current_time = end
                current_loc = loc
            if s.check() == sat:
                model = s.model()
                itinerary = []
                current_loc = 'Haight-Ashbury'
                current_time = 540
                for friend in perm:
                    info = friends_info[friend]
                    loc = info['location']
                    travel_time = get_travel_time(current_loc, loc)
                    arrival_time = current_time + travel_time
                    start = model.evaluate(start_times[friend]).as_long()
                    end = start + info['required_duration']
                    start_str = time_to_str(start)
                    end_str = time_to_str(end)
                    itinerary.append({"action": "meet", "person": friend, "start_time": start_str, "end_time": end_str})
                    current_time = end
                    current_loc = loc
                print(json.dumps({"itinerary": itinerary}))
                return

if __name__ == "__main__":
    main()