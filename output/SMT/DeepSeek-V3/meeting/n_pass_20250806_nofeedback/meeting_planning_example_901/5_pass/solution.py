from z3 import *
import json

def solve_scheduling_problem():
    s = Solver()

    # Define friends and their locations
    friends = {
        'Emily': 'Pacific Heights',
        'Helen': 'North Beach',
        'Kimberly': 'Golden Gate Park',
        'James': 'Embarcadero',
        'Linda': 'Haight-Ashbury',
        'Paul': 'Fisherman\'s Wharf',
        'Anthony': 'Mission District',
        'Nancy': 'Alamo Square',
        'William': 'Bayview',
        'Margaret': 'Richmond District'
    }

    # Travel times between locations (minutes)
    travel_times = {
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Richmond District'): 14,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Embarcadero'): 10,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Richmond District'): 12,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Bayview'): 25,
        ('North Beach', 'Richmond District'): 18,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Alamo Square'): 9,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Mission District'): 20,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Richmond District'): 21,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Alamo Square'): 21,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Mission District', 'Alamo Square'): 10,
        ('Mission District', 'Bayview'): 14,
        ('Mission District', 'Richmond District'): 20,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Richmond District'): 11,
        ('Bayview', 'Richmond District'): 27
    }

    # Time windows (minutes since 9:00 AM)
    time_windows = {
        'Emily': (555, 825, 120),
        'Helen': (825, 1080, 30),
        'Kimberly': (1080, 1170, 75),
        'James': (630, 690, 30),
        'Linda': (450, 1095, 15),
        'Paul': (855, 1080, 90),
        'Anthony': (480, 855, 105),
        'Nancy': (510, 825, 120),
        'William': (1050, 1170, 120),
        'Margaret': (945, 1080, 45)
    }

    # Create meeting variables
    meetings = {}
    for friend in friends:
        start = Int(f'start_{friend}')
        end = Int(f'end_{friend}')
        meetings[friend] = (start, end)
        s.add(start >= time_windows[friend][0])
        s.add(end <= time_windows[friend][1])
        s.add(end - start >= time_windows[friend][2])

    # Create sequence variables
    sequence = {f: Int(f'seq_{f}') for f in friends}
    for f in friends:
        s.add(sequence[f] >= 0)
        s.add(sequence[f] < len(friends))
    s.add(Distinct([sequence[f] for f in friends]))

    # Create variables for arrival and departure times
    arrival = {f: Int(f'arr_{f}') for f in friends}
    departure = {f: Int(f'dep_{f}') for f in friends}

    # Starting point
    first_friend = [f for f in friends if sequence[f] == 0][0]
    s.add(arrival[first_friend] == 540 + travel_times[('Russian Hill', friends[first_friend])])
    s.add(departure[first_friend] == arrival[first_friend] + (meetings[first_friend][1] - meetings[first_friend][0]))

    # Sequence constraints
    for f in friends:
        for other_f in friends:
            if f != other_f:
                # If other_f comes right before f
                s.add(Implies(sequence[other_f] + 1 == sequence[f],
                    arrival[f] >= departure[other_f] + travel_times.get((friends[other_f], friends[f]), 0)))

    # Meeting time constraints
    for f in friends:
        s.add(meetings[f][0] >= arrival[f])
        s.add(meetings[f][1] <= departure[f])

    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for f in friends:
            start = m.evaluate(meetings[f][0]).as_long()
            end = m.evaluate(meetings[f][1]).as_long()
            start_hh = (540 + start) // 60
            start_mm = (540 + start) % 60
            end_hh = (540 + end) // 60
            end_mm = (540 + end) % 60
            itinerary.append({
                "action": "meet",
                "person": f,
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))