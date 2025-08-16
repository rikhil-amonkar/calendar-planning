import itertools
from z3 import Solver, Int, sat, model

def solve_schedule():
    friends_list = ['Stephanie', 'Sandra', 'Brian', 'Jason']
    friends_data = {
        'Stephanie': {
            'location': 'Mission District',
            'available_start': 8 * 60 + 15,
            'available_end': 13 * 60 + 45,
            'min_duration': 90
        },
        'Sandra': {
            'location': 'Bayview',
            'available_start': 13 * 60,
            'available_end': 19 * 60 + 30,
            'min_duration': 15
        },
        'Brian': {
            'location': 'Russian Hill',
            'available_start': 12 * 60 + 15,
            'available_end': 16 * 60,
            'min_duration': 120
        },
        'Jason': {
            'location': "Fisherman's Wharf",
            'available_start': 8 * 60 + 30,
            'available_end': 17 * 60 + 45,
            'min_duration': 60
        }
    }
    travel_times = {
        'Haight-Ashbury': {
            'Mission District': 11,
            'Bayview': 18,
            'Pacific Heights': 12,
            'Russian Hill': 17,
            "Fisherman's Wharf": 23
        },
        'Mission District': {
            'Haight-Ashbury': 12,
            'Bayview': 15,
            'Pacific Heights': 16,
            'Russian Hill': 15,
            "Fisherman's Wharf": 22
        },
        'Bayview': {
            'Haight-Ashbury': 19,
            'Mission District': 13,
            'Pacific Heights': 23,
            'Russian Hill': 23,
            "Fisherman's Wharf": 25
        },
        'Pacific Heights': {
            'Haight-Ashbury': 11,
            'Mission District': 15,
            'Bayview': 22,
            'Russian Hill': 7,
            "Fisherman's Wharf": 13
        },
        'Russian Hill': {
            'Haight-Ashbury': 17,
            'Mission District': 16,
            'Bayview': 23,
            'Pacific Heights': 7,
            "Fisherman's Wharf": 7
        },
        "Fisherman's Wharf": {
            'Haight-Ashbury': 22,
            'Mission District': 22,
            'Bayview': 26,
            'Pacific Heights': 12,
            'Russian Hill': 7
        }
    }

    for perm in itertools.permutations(friends_list):
        s = Solver()
        starts = []
        ends = []
        previous_end = 540  # 9:00 AM in minutes
        previous_location = 'Haight-Ashbury'

        for i, name in enumerate(perm):
            friend = friends_data[name]
            location = friend['location']
            duration = friend['min_duration']
            available_end = friend['available_end']

            start = Int(f'start_{name}_{i}')
            end = Int(f'end_{name}_{i}')
            starts.append(start)
            ends.append(end)

            travel_time = travel_times[previous_location][location]
            arrival_time = previous_end + travel_time

            s.add(start >= arrival_time)
            s.add(end == start + duration)
            s.add(end <= available_end)

            previous_end = end
            previous_location = location

        if s.check() == sat:
            model = s.model()
            itinerary = []
            for i, name in enumerate(perm):
                start_val = model.evaluate(starts[i]).as_long()
                end_val = model.evaluate(ends[i]).as_long()

                start_h = start_val // 60
                start_m = start_val % 60
                end_h = end_val // 60
                end_m = end_val % 60

                start_time = f"{start_h:02d}:{start_m:02d}"
                end_time = f"{end_h:02d}:{end_m:02d}"

                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })

            return {"itinerary": itinerary}

    return {"itinerary": []}

# Example usage (not part of the JSON output)
# result = solve_schedule()
# print(result)