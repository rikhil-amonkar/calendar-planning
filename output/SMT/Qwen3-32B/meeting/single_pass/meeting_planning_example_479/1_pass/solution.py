from z3 import *
import itertools

def to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def is_feasible(perm, travel_times):
    solver = Solver()
    start_vars = []
    for i, friend in enumerate(perm):
        name = friend['name']
        start_var = Int(f'start_{name}')
        start_vars.append(start_var)
    for i in range(len(perm)):
        friend = perm[i]
        loc = friend['location']
        min_duration = friend['min_duration']
        available_start_minutes = to_minutes(friend['available_start'])
        available_end_minutes = to_minutes(friend['available_end'])

        start_var = start_vars[i]
        end_var = start_var + min_duration

        # end_var must be <= available_end_minutes
        solver.add(end_var <= available_end_minutes)

        if i == 0:
            # First friend
            arrival_time = 9 * 60  # 9:00 AM
            travel_time = travel_times[('Embarcadero', loc)]
            arrival_at_location = arrival_time + travel_time
            solver.add(start_var >= arrival_at_location)
        else:
            prev_friend = perm[i-1]
            prev_loc = prev_friend['location']
            prev_start_var = start_vars[i-1]
            prev_duration = prev_friend['min_duration']
            prev_end_var = prev_start_var + prev_duration
            travel_time = travel_times[(prev_loc, loc)]
            solver.add(start_var >= prev_end_var + travel_time)

        # start_var must be >= available_start_minutes
        solver.add(start_var >= available_start_minutes)

    result = solver.check()
    if result == sat:
        model = solver.model()
        times = []
        for i in range(len(perm)):
            start = model[start_vars[i]].as_long()
            duration = perm[i]['min_duration']
            end = start + duration
            times.append( (start, end) )
        return True, times
    else:
        return False, None

def find_best_itinerary(friends_data, travel_times):
    for subset_size in range(len(friends_data), 0, -1):
        for subset in itertools.combinations(friends_data, subset_size):
            for perm in itertools.permutations(subset):
                feasible, times = is_feasible(perm, travel_times)
                if feasible:
                    itinerary = []
                    for i in range(len(perm)):
                        friend = perm[i]
                        start_minutes = times[i][0]
                        end_minutes = times[i][1]
                        start_time = to_time_str(start_minutes)
                        end_time = to_time_str(end_minutes)
                        itinerary.append({
                            "action": "meet",
                            "person": friend['name'],
                            "start_time": start_time,
                            "end_time": end_time
                        })
                    return {"itinerary": itinerary}
    return {"itinerary": []}

# Define friends data
friends_data = [
    {
        'name': 'Mary',
        'location': 'Golden Gate Park',
        'available_start': '08:45',
        'available_end': '11:45',
        'min_duration': 45,
    },
    {
        'name': 'Kevin',
        'location': 'Haight-Ashbury',
        'available_start': '10:15',
        'available_end': '16:15',
        'min_duration': 90,
    },
    {
        'name': 'Deborah',
        'location': 'Bayview',
        'available_start': '15:00',
        'available_end': '19:15',
        'min_duration': 120,
    },
    {
        'name': 'Stephanie',
        'location': 'Presidio',
        'available_start': '10:00',
        'available_end': '17:15',
        'min_duration': 120,
    },
    {
        'name': 'Emily',
        'location': 'Financial District',
        'available_start': '11:30',
        'available_end': '21:45',
        'min_duration': 105,
    },
]

# Define travel times
travel_times = {
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Financial District'): 5,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Financial District'): 19,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Financial District'): 23,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Presidio'): 22,
}

# Find the best itinerary
best_itinerary = find_best_itinerary(friends_data, travel_times)
print(best_itinerary)