import itertools
import json
from z3 import *

def format_time(m):
    total_mins = 540 + m  # 9 AM is 540 mins since midnight
    hours = total_mins // 60
    minutes = total_mins % 60
    return f"{hours}:{minutes:02d}"

# Define travel times between locations
travel_times = {
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Alamo Square'): 16,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Alamo Square'): 15,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Union Square'): 14,
}

friends_data = {
    'Sarah': {
        'location': 'North Beach',
        'available_start': 420,  # 4 PM
        'available_end': 555,    # 6:15 PM
        'min_duration': 60
    },
    'Jeffrey': {
        'location': 'Union Square',
        'available_start': 360,  # 3 PM
        'available_end': 780,    # 10 PM
        'min_duration': 75
    },
    'Brian': {
        'location': 'Alamo Square',
        'available_start': 420,  # 4 PM
        'available_end': 510,    # 5:30 PM
        'min_duration': 75
    }
}

max_solution = None
max_num_friends = 0

# Check for 3 friends
friends_list = ['Sarah', 'Jeffrey', 'Brian']
for perm in itertools.permutations(friends_list):
    solver = Solver()
    prev_location = 'Sunset District'
    prev_end = 0  # start time is 9:00 AM (0 mins since 9 AM)
    for friend in perm:
        loc = friends_data[friend]['location']
        travel_time = travel_times[(prev_location, loc)]
        arrival_time = prev_end + travel_time
        start_var = Int(f'start_{friend}')
        end_var = Int(f'end_{friend}')
        available_start = friends_data[friend]['available_start']
        available_end = friends_data[friend]['available_end']
        min_duration = friends_data[friend]['min_duration']
        # Add constraints
        solver.add(start_var >= arrival_time)
        solver.add(start_var >= available_start)
        solver.add(end_var == start_var + min_duration)
        solver.add(end_var <= available_end)
        # Update for next step
        prev_location = loc
        prev_end = end_var
    # Check if the solver is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for friend in perm:
            start = model.eval(Int(f'start_{friend}')).as_long()
            end = model.eval(Int(f'end_{friend}')).as_long()
            start_time = format_time(start)
            end_time = format_time(end)
            loc = friends_data[friend]['location']
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": friend,
                "start_time": start_time,
                "end_time": end_time
            })
        max_solution = itinerary
        max_num_friends = len(perm)
        # Output and exit early if found
        print(json.dumps({"itinerary": max_solution}))
        exit()

# Check for 2 friends
for subset_size in [2]:
    for subset in itertools.combinations(friends_list, subset_size):
        for perm in itertools.permutations(subset):
            solver = Solver()
            prev_location = 'Sunset District'
            prev_end = 0
            for friend in perm:
                loc = friends_data[friend]['location']
                travel_time = travel_times[(prev_location, loc)]
                arrival_time = prev_end + travel_time
                start_var = Int(f'start_{friend}')
                end_var = Int(f'end_{friend}')
                available_start = friends_data[friend]['available_start']
                available_end = friends_data[friend]['available_end']
                min_duration = friends_data[friend]['min_duration']
                solver.add(start_var >= arrival_time)
                solver.add(start_var >= available_start)
                solver.add(end_var == start_var + min_duration)
                solver.add(end_var <= available_end)
                prev_location = loc
                prev_end = end_var
            if solver.check() == sat:
                model = solver.model()
                itinerary = []
                for friend in perm:
                    start = model.eval(Int(f'start_{friend}')).as_long()
                    end = model.eval(Int(f'end_{friend}')).as_long()
                    start_time = format_time(start)
                    end_time = format_time(end)
                    loc = friends_data[friend]['location']
                    itinerary.append({
                        "action": "meet",
                        "location": loc,
                        "person": friend,
                        "start_time": start_time,
                        "end_time": end_time
                    })
                if len(itinerary) > max_num_friends:
                    max_solution = itinerary
                    max_num_friends = len(itinerary)
                elif len(itinerary) == max_num_friends and max_solution is None:
                    max_solution = itinerary
    if max_solution is not None:
        break

# Check for 1 friend
if max_solution is None:
    for friend in friends_list:
        solver = Solver()
        prev_location = 'Sunset District'
        prev_end = 0
        loc = friends_data[friend]['location']
        travel_time = travel_times[(prev_location, loc)]
        arrival_time = prev_end + travel_time
        start_var = Int(f'start_{friend}')
        end_var = Int(f'end_{friend}')
        available_start = friends_data[friend]['available_start']
        available_end = friends_data[friend]['available_end']
        min_duration = friends_data[friend]['min_duration']
        solver.add(start_var >= arrival_time)
        solver.add(start_var >= available_start)
        solver.add(end_var == start_var + min_duration)
        solver.add(end_var <= available_end)
        if solver.check() == sat:
            model = solver.model()
            start = model.eval(start_var).as_long()
            end = model.eval(end_var).as_long()
            start_time = format_time(start)
            end_time = format_time(end)
            max_solution = [{
                "action": "meet",
                "location": loc,
                "person": friend,
                "start_time": start_time,
                "end_time": end_time
            }]
            break

# Output the result
if max_solution:
    print(json.dumps({"itinerary": max_solution}))
else:
    print(json.dumps({"itinerary": []}))