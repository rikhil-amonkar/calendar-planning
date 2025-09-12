import z3

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    friends = [
        {
            'index': 0,
            'name': 'Mark',
            'location': 'Marina District',
            'available_start': 18 * 60 + 45,  # 6:45 PM
            'available_end': 21 * 60,         # 9:00 PM
            'min_duration': 90
        },
        {
            'index': 1,
            'name': 'Karen',
            'location': 'Financial District',
            'available_start': 9 * 60 + 30,   # 9:30 AM
            'available_end': 12 * 60 + 45,    # 12:45 PM
            'min_duration': 90
        },
        {
            'index': 2,
            'name': 'Barbara',
            'location': 'Alamo Square',
            'available_start': 10 * 60,       # 10:00 AM
            'available_end': 19 * 60 + 30,    # 7:30 PM
            'min_duration': 90
        },
        {
            'index': 3,
            'name': 'Nancy',
            'location': 'Golden Gate Park',
            'available_start': 16 * 60 + 45,  # 4:45 PM
            'available_end': 20 * 60,         # 8:00 PM
            'min_duration': 105
        },
        {
            'index': 4,
            'name': 'David',
            'location': 'The Castro',
            'available_start': 9 * 60,        # 9:00 AM
            'available_end': 18 * 60,         # 6:00 PM
            'min_duration': 120
        },
        {
            'index': 5,
            'name': 'Linda',
            'location': 'Bayview',
            'available_start': 18 * 60 + 15,  # 6:15 PM
            'available_end': 19 * 60 + 45,    # 7:45 PM
            'min_duration': 45
        },
        {
            'index': 6,
            'name': 'Kevin',
            'location': 'Sunset District',
            'available_start': 10 * 60,       # 10:00 AM
            'available_end': 17 * 60 + 45,    # 5:45 PM
            'min_duration': 120
        },
        {
            'index': 7,
            'name': 'Matthew',
            'location': 'Haight-Ashbury',
            'available_start': 10 * 60 + 15,  # 10:15 AM
            'available_end': 15 * 60 + 30,    # 3:30 PM
            'min_duration': 45
        },
        {
            'index': 8,
            'name': 'Andrew',
            'location': 'Nob Hill',
            'available_start': 11 * 60 + 45,  # 11:45 AM
            'available_end': 16 * 60 + 45,    # 4:45 PM
            'min_duration': 105
        }
    ]
    
    travel_times = {
        # From Russian Hill
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'Financial District'): 11,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Nob Hill'): 5,
        # From Marina District
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Nob Hill'): 12,
        # From Financial District
        ('Financial District', 'Russian Hill'): 11,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'The Castro'): 20,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Sunset District'): 30,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Financial District', 'Nob Hill'): 8,
        # From Alamo Square
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Nob Hill'): 11,
        # From Golden Gate Park
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Alamo Square'): 9,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Nob Hill'): 20,
        # From The Castro
        ('The Castro', 'Russian Hill'): 18,
        ('The Castro', 'Marina District'): 21,
        ('The Castro', 'Financial District'): 21,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Bayview'): 19,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Nob Hill'): 16,
        # From Bayview
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'The Castro'): 19,
        ('Bayview', 'Sunset District'): 23,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Nob Hill'): 20,
        # From Sunset District
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Nob Hill'): 27,
        # From Haight-Ashbury
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        # From Nob Hill
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Bayview'): 19,
        ('Nob Hill', 'Sunset District'): 24,
        ('Nob Hill', 'Haight-Ashbury'): 13,
    }
    
    friend_locations = {f['index']: f['location'] for f in friends}
    
    travel_time_from_russian_hill = []
    for i in range(9):
        loc = friend_locations[i]
        travel_time_from_russian_hill.append(travel_times[('Russian Hill', loc)])
    
    travel_time_between_friends = []
    for i in range(9):
        row = []
        for j in range(9):
            loc_i = friend_locations[i]
            loc_j = friend_locations[j]
            row.append(travel_times[(loc_i, loc_j)])
        travel_time_between_friends.append(row)
    
    solver = z3.Optimize()
    
    travel_time_from_russian_hill_func = z3.Function('travel_time_from_russian_hill_func', z3.IntSort(), z3.IntSort())
    travel_time_func = z3.Function('travel_time_func', z3.IntSort(), z3.IntSort(), z3.IntSort())
    
    for i in range(9):
        solver.add(travel_time_from_russian_hill_func(i) == travel_time_from_russian_hill[i])
    
    for i in range(9):
        for j in range(9):
            solver.add(travel_time_func(i, j) == travel_time_between_friends[i][j])
    
    num_steps = 9
    friend_vars = [z3.Int(f'friend_{i}') for i in range(num_steps)]
    start_vars = [z3.Int(f'start_{i}') for i in range(num_steps)]
    end_vars = [z3.Int(f'end_{i}') for i in range(num_steps)]
    arrival_vars = [z3.Int(f'arrival_{i}') for i in range(num_steps)]
    
    for f in range(9):
        sum_expr = z3.Sum([z3.If(z3.And(friend_vars[i] == f, friend_vars[i] != -1), 1, 0) for i in range(num_steps)])
        solver.add(sum_expr <= 1)
    
    for i in range(num_steps):
        if i == 0:
            solver.add(arrival_vars[i] == 540 + travel_time_from_russian_hill_func(friend_vars[i]))
        else:
            solver.add(arrival_vars[i] == end_vars[i-1] + travel_time_func(friend_vars[i-1], friend_vars[i]))
        
        f = friend_vars[i]
        available_start_expr = 0
        available_end_expr = 0
        min_duration_expr = 0
        for idx in range(9):
            available_start_expr = z3.If(f == idx, friends[idx]['available_start'], available_start_expr)
            available_end_expr = z3.If(f == idx, friends[idx]['available_end'], available_end_expr)
            min_duration_expr = z3.If(f == idx, friends[idx]['min_duration'], min_duration_expr)
        
        solver.add(z3.Implies(f != -1, start_vars[i] >= arrival_vars[i]))
        solver.add(z3.Implies(f != -1, start_vars[i] >= available_start_expr))
        solver.add(z3.Implies(f != -1, end_vars[i] - start_vars[i] >= min_duration_expr))
        solver.add(z3.Implies(f != -1, end_vars[i] <= available_end_expr))
    
    count = z3.Sum([z3.If(friend_vars[i] != -1, 1, 0) for i in range(num_steps)])
    solver.maximize(count)
    
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        for i in range(num_steps):
            model_f = model.eval(friend_vars[i])
            if model_f != -1:
                friend_idx = model_f.as_long()
                start_time = model.eval(start_vars[i]).as_long()
                end_time = model.eval(end_vars[i]).as_long()
                name = friends[friend_idx]['name']
                location = friends[friend_idx]['location']
                start_str = minutes_to_time_str(start_time)
                end_str = minutes_to_time_str(end_time)
                itinerary.append({
                    'action': 'meet',
                    'location': location,
                    'person': name,
                    'start_time': start_str,
                    'end_time': end_str
                })
        import json
        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == '__main__':
    main()