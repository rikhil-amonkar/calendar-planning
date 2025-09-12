import itertools
from z3 import *
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    friends = [
        {
            'name': 'Karen',
            'location': 'Nob Hill',
            'available_start': 21 * 60 + 15,  # 9:15 PM
            'available_end': 21 * 60 + 45,    # 9:45 PM
            'duration': 30
        },
        {
            'name': 'Joseph',
            'location': 'Haight-Ashbury',
            'available_start': 12 * 60 + 30,  # 12:30 PM
            'available_end': 19 * 60 + 45,    # 7:45 PM
            'duration': 90
        },
        {
            'name': 'Sandra',
            'location': 'Chinatown',
            'available_start': 7 * 60 + 15,   # 7:15 AM
            'available_end': 19 * 60 + 15,    # 7:15 PM
            'duration': 75
        },
        {
            'name': 'Nancy',
            'location': 'Marina District',
            'available_start': 11 * 60 + 0,   # 11:00 AM
            'available_end': 20 * 60 + 15,    # 8:15 PM
            'duration': 105
        }
    ]

    travel_time_dict = {
        'Union Square': {
            'Nob Hill': 9,
            'Haight-Ashbury': 18,
            'Chinatown': 7,
            'Marina District': 18,
        },
        'Nob Hill': {
            'Union Square': 7,
            'Haight-Ashbury': 13,
            'Chinatown': 6,
            'Marina District': 11,
        },
        'Haight-Ashbury': {
            'Union Square': 17,
            'Nob Hill': 15,
            'Chinatown': 19,
            'Marina District': 17,
        },
        'Chinatown': {
            'Union Square': 7,
            'Nob Hill': 8,
            'Haight-Ashbury': 19,
            'Marina District': 12,
        },
        'Marina District': {
            'Union Square': 16,
            'Nob Hill': 12,
            'Haight-Ashbury': 16,
            'Chinatown': 16,
        },
    }

    # Check permutations in order of largest subset first
    for subset_size in range(4, 0, -1):
        for subset in itertools.combinations(friends, subset_size):
            for perm in itertools.permutations(subset):
                solver = Solver()
                starts = []
                ends = []
                for friend in perm:
                    start = Int(f"start_{friend['name']}")
                    end = Int(f"end_{friend['name']}")
                    starts.append(start)
                    ends.append(end)
                # Add constraints
                # First friend
                first_friend = perm[0]
                from_loc = 'Union Square'
                to_loc = first_friend['location']
                travel_time = travel_time_dict[from_loc][to_loc]
                solver.add(starts[0] >= 540 + travel_time)
                solver.add(starts[0] >= first_friend['available_start'])
                solver.add(ends[0] == starts[0] + first_friend['duration'])
                solver.add(ends[0] <= first_friend['available_end'])
                # Subsequent friends
                for i in range(1, len(perm)):
                    prev_loc = perm[i-1]['location']
                    curr_loc = perm[i]['location']
                    travel_time = travel_time_dict[prev_loc][curr_loc]
                    solver.add(starts[i] >= ends[i-1] + travel_time)
                    solver.add(starts[i] >= perm[i]['available_start'])
                    solver.add(ends[i] == starts[i] + perm[i]['duration'])
                    solver.add(ends[i] <= perm[i]['available_end'])
                # Check if feasible
                if solver.check() == sat:
                    model = solver.model()
                    itinerary = []
                    for i in range(len(perm)):
                        friend = perm[i]
                        start_val = model.evaluate(starts[i]).as_long()
                        end_val = model.evaluate(ends[i]).as_long()
                        start_time = minutes_to_time(start_val)
                        end_time = minutes_to_time(end_val)
                        itinerary.append({
                            "action": "meet",
                            "location": friend['location'],
                            "person": friend['name'],
                            "start_time": start_time,
                            "end_time": end_time
                        })
                    print(json.dumps({"itinerary": itinerary}, indent=2))
                    return

    # If no solution found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()