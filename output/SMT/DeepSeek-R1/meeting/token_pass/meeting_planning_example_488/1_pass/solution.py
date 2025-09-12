import itertools
from z3 import *

def main():
    # Travel times dictionary
    travel_times = {
        'Pacific Heights': {
            'Nob Hill': 8,
            'Russian Hill': 7,
            'The Castro': 16,
            'Sunset District': 21,
            'Haight-Ashbury': 11
        },
        'Nob Hill': {
            'Pacific Heights': 8,
            'Russian Hill': 5,
            'The Castro': 17,
            'Sunset District': 25,
            'Haight-Ashbury': 13
        },
        'Russian Hill': {
            'Pacific Heights': 7,
            'Nob Hill': 5,
            'The Castro': 21,
            'Sunset District': 23,
            'Haight-Ashbury': 17
        },
        'The Castro': {
            'Pacific Heights': 16,
            'Nob Hill': 16,
            'Russian Hill': 18,
            'Sunset District': 17,
            'Haight-Ashbury': 6
        },
        'Sunset District': {
            'Pacific Heights': 21,
            'Nob Hill': 27,
            'Russian Hill': 24,
            'The Castro': 17,
            'Haight-Ashbury': 15
        },
        'Haight-Ashbury': {
            'Pacific Heights': 12,
            'Nob Hill': 15,
            'Russian Hill': 17,
            'The Castro': 6,
            'Sunset District': 15
        }
    }

    # Friend information: name, location, available_start, available_end, min_duration
    # All times in minutes from 9:00 AM (9:00 AM is 0)
    friends_info = [
        {
            'name': 'Ronald',
            'location': 'Nob Hill',
            'available_start': 60,   # 10:00 AM
            'available_end': 480,     # 5:00 PM
            'min_duration': 105
        },
        {
            'name': 'Sarah',
            'location': 'Russian Hill',
            'available_start': -105,  # 7:15 AM
            'available_end': 30,      # 9:30 AM
            'min_duration': 45
        },
        {
            'name': 'Helen',
            'location': 'The Castro',
            'available_start': 270,   # 1:30 PM
            'available_end': 480,     # 5:00 PM
            'min_duration': 120
        },
        {
            'name': 'Joshua',
            'location': 'Sunset District',
            'available_start': 315,   # 2:15 PM
            'available_end': 570,     # 7:30 PM
            'min_duration': 90
        },
        {
            'name': 'Margaret',
            'location': 'Haight-Ashbury',
            'available_start': 75,    # 10:15 AM
            'available_end': 780,     # 10:00 PM
            'min_duration': 60
        }
    ]

    # Since Sarah is not feasible (as determined by initial analysis), we exclude her
    feasible_friends = [f for f in friends_info if f['name'] != 'Sarah']
    n = len(feasible_friends)

    # We'll try to find the largest feasible subset
    best_schedule = None
    best_size = 0
    best_model = None

    # Try all subset sizes from n down to 1
    for k in range(n, 0, -1):
        for subset in itertools.combinations(feasible_friends, k):
            solver = Solver()
            meeting_vars = {}
            start_vars = {}
            end_vars = {}

            # Create variables for each friend in the subset
            for friend in subset:
                name = friend['name']
                start_var = Real(f'start_{name}')
                meet_var = Bool(f'meet_{name}')
                meeting_vars[name] = meet_var
                start_vars[name] = start_var
                end_vars[name] = start_var + friend['min_duration']

                # Constraints if we meet this friend
                solver.add(Implies(meet_var, start_var >= friend['available_start']))
                solver.add(Implies(meet_var, end_vars[name] <= friend['available_end']))
                solver.add(Implies(meet_var, start_var >= travel_times['Pacific Heights'][friend['location']]))

            # Pairwise constraints for each pair of friends in the subset
            for i, friend1 in enumerate(subset):
                for friend2 in subset[i+1:]:
                    name1 = friend1['name']
                    name2 = friend2['name']
                    loc1 = friend1['location']
                    loc2 = friend2['location']
                    travel1to2 = travel_times[loc1][loc2]
                    travel2to1 = travel_times[loc2][loc1]

                    # If both meetings happen, then one must be after the other with travel time
                    constraint = Implies(
                        And(meeting_vars[name1], meeting_vars[name2]),
                        Or(
                            end_vars[name1] + travel1to2 <= start_vars[name2],
                            end_vars[name2] + travel2to1 <= start_vars[name1]
                        )
                    )
                    solver.add(constraint)

            # Assert that we meet all friends in the subset
            solver.add([meeting_vars[f['name']] for f in subset])

            if solver.check() == sat:
                model = solver.model()
                # We found a feasible subset of size k
                best_size = k
                best_model = model
                best_subset = subset
                break
        if best_size == k:
            break

    # If no meeting is feasible, return empty itinerary
    if best_size == 0:
        print('{"itinerary": []}')
        return

    # Extract the schedule from the model
    itinerary = []
    for friend in best_subset:
        name = friend['name']
        start_val = best_model.eval(start_vars[name]).as_decimal(0)
        start_minutes = float(start_val) * 60  # Convert to minutes (Z3 real to float)
        end_minutes = start_minutes + friend['min_duration']

        # Convert minutes to time string (from minutes since 9:00)
        start_time = minutes_to_time(start_minutes)
        end_time = minutes_to_time(end_minutes)

        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": name,
            "start_time": start_time,
            "end_time": end_time
        })

    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])

    # Output as JSON
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))

def minutes_to_time(minutes):
    total_minutes = int(round(float(minutes)))
    hours = total_minutes // 60
    minutes = total_minutes % 60
    time_str = f"{hours}:{minutes:02d}"
    return time_str

if __name__ == '__main__':
    main()