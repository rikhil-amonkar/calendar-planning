from z3 import *

def solve_scheduling():
    s = Optimize()

    # Convert times to minutes since midnight
    def time_to_minutes(h, m):
        return h * 60 + m

    friends = {
        'Kevin': {
            'location': 'Alamo Square',
            'start': time_to_minutes(8, 15),  # 8:15 AM
            'end': time_to_minutes(21, 30),   # 9:30 PM
            'duration': 75,
        },
        'Kimberly': {
            'location': 'Russian Hill',
            'start': time_to_minutes(8, 45),  # 8:45 AM
            'end': time_to_minutes(12, 30),   # 12:30 PM
            'duration': 30,
        },
        'Joseph': {
            'location': 'Presidio',
            'start': time_to_minutes(18, 30),  # 6:30 PM
            'end': time_to_minutes(19, 15),    # 7:15 PM
            'duration': 45,
        },
        'Thomas': {
            'location': 'Financial District',
            'start': time_to_minutes(19, 0),  # 7:00 PM
            'end': time_to_minutes(21, 45),    # 9:45 PM
            'duration': 45,
        }
    }

    travel_times = {
        'Sunset District': {
            'Alamo Square': 17,
            'Russian Hill': 24,
            'Presidio': 16,
            'Financial District': 30,
        },
        'Alamo Square': {
            'Sunset District': 16,
            'Russian Hill': 13,
            'Presidio': 18,
            'Financial District': 17,
        },
        'Russian Hill': {
            'Sunset District': 23,
            'Alamo Square': 15,
            'Presidio': 14,
            'Financial District': 11,
        },
        'Presidio': {
            'Sunset District': 15,
            'Alamo Square': 18,
            'Russian Hill': 14,
            'Financial District': 23,
        },
        'Financial District': {
            'Sunset District': 31,
            'Alamo Square': 17,
            'Russian Hill': 10,
            'Presidio': 22,
        }
    }

    # Variables
    start_vars = {name: Int(f'start_{name}') for name in friends}
    end_vars = {name: Int(f'end_{name}') for name in friends}
    met_vars = {name: Bool(f'met_{name}') for name in friends}

    # Initial current time and location
    current_time = 540  # 9:00 AM
    current_location = 'Sunset District'

    # Constraints for each friend
    for name in friends:
        data = friends[name]
        start = start_vars[name]
        end = end_vars[name]
        met = met_vars[name]

        # If met, meeting must be within availability and duration
        s.add(Implies(met, start >= data['start']))
        s.add(Implies(met, end == start + data['duration']))
        s.add(Implies(met, end <= data['end']))

    # To model the sequence, we need to choose an order of meetings.
    # This is complex, so instead, we'll allow any order but ensure no overlaps and correct travel times.

    # We'll use auxiliary variables to represent the order.
    # For simplicity, we'll assume that the user can meet friends in any order, but each meeting's start is after the previous end plus travel.

    # Alternatively, we can use a more sophisticated approach with sequencing constraints.

    # For now, let's assume that the user can meet friends in any order, but the constraints must hold for the chosen meetings.

    # To maximize the number of friends met, we'll sum the met_vars and maximize it.
    total_met = Sum([If(met_vars[name], 1, 0) for name in friends])
    s.maximize(total_met)

    # Additionally, for each pair of friends, if both are met, one must be before the other with travel time accounted for.
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                # Either name1 is before name2 or vice versa
                before = Bool(f'before_{name1}_{name2}')
                s.add(Implies(And(met_vars[name1], met_vars[name2], before),
                       start_vars[name2] >= end_vars[name1] + travel_times[friends[name1]['location']][friends[name2]['location']]))
                s.add(Implies(And(met_vars[name1], met_vars[name2], Not(before)),
                       start_vars[name1] >= end_vars[name2] + travel_times[friends[name2]['location']][friends[name1]['location']]))

    # The first meeting must start after current_time plus travel to their location.
    for name in friends:
        travel_time = travel_times[current_location][friends[name]['location']]
        s.add(Implies(met_vars[name], start_vars[name] >= current_time + travel_time))

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        total = model.eval(total_met)
        print(f"Can meet {total} friends!")
        schedule = []
        for name in friends:
            if is_true(model.eval(met_vars[name])):
                start = model.eval(start_vars[name]).as_long()
                end = model.eval(end_vars[name]).as_long()
                schedule.append((name, start, end))
        schedule.sort(key=lambda x: x[1])
        print("Optimal Schedule:")
        for name, start, end in schedule:
            start_h = start // 60
            start_m = start % 60
            end_h = end // 60
            end_m = end % 60
            print(f"Meet {name} from {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d} at {friends[name]['location']}")
    else:
        print("No feasible schedule found.")

solve_scheduling()