import z3
import json

def solve():
    friends = [
        {
            'name': 'Charles',
            'location': 'Bayview',
            'available_start': 11 * 60 + 30,  # 690
            'available_end': 14 * 60 + 30,    # 870
            'required_duration': 45,
        },
        {
            'name': 'Robert',
            'location': 'Sunset District',
            'available_start': 16 * 60 + 45,  # 1005
            'available_end': 21 * 60 + 0,     # 1260
            'required_duration': 30,
        },
        {
            'name': 'Karen',
            'location': 'Richmond District',
            'available_start': 19 * 60 + 15,  # 1155
            'available_end': 21 * 60 + 30,    # 1290
            'required_duration': 60,
        },
        {
            'name': 'Rebecca',
            'location': 'Nob Hill',
            'available_start': 16 * 60 + 15,  # 975
            'available_end': 20 * 60 + 30,    # 1230
            'required_duration': 90,
        },
        {
            'name': 'Margaret',
            'location': 'Chinatown',
            'available_start': 14 * 60 + 15,  # 855
            'available_end': 19 * 60 + 45,    # 1185
            'required_duration': 120,
        },
        {
            'name': 'Patricia',
            'location': 'Haight-Ashbury',
            'available_start': 14 * 60 + 30,  # 870
            'available_end': 20 * 60 + 30,    # 1230
            'required_duration': 45,
        },
        {
            'name': 'Mark',
            'location': 'North Beach',
            'available_start': 14 * 60 + 0,   # 840
            'available_end': 18 * 60 + 30,    # 1110
            'required_duration': 105,
        },
        {
            'name': 'Melissa',
            'location': 'Russian Hill',
            'available_start': 13 * 60 + 0,   # 780
            'available_end': 19 * 60 + 45,    # 1185
            'required_duration': 30,
        },
        {
            'name': 'Laura',
            'location': 'Embarcadero',
            'available_start': 7 * 60 + 45,   # 465
            'available_end': 13 * 60 + 15,    # 795
            'required_duration': 105,
        },
    ]

    travel_times_dict = {
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'Embarcadero'): 14,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Sunset District'): 23,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'North Beach'): 22,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Embarcadero'): 19,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Nob Hill'): 27,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'North Beach'): 28,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Embarcadero'): 30,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'Bayview'): 27,
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Chinatown'): 20,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Russian Hill'): 13,
        ('Richmond District', 'Embarcadero'): 19,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Bayview'): 19,
        ('Nob Hill', 'Sunset District'): 24,
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Richmond District'): 20,
        ('Chinatown', 'Nob Hill'): 9,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Embarcadero'): 5,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('North Beach', 'Marina District'): 9,
        ('North Beach', 'Bayview'): 25,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Embarcadero'): 6,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Richmond District'): 14,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Embarcadero', 'Marina District'): 12,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Russian Hill'): 8,
    }

    locations = [f['location'] for f in friends]
    friend_travel_time = [[0 for _ in range(9)] for _ in range(9)]
    for a in range(9):
        for b in range(9):
            loc_a = locations[a]
            loc_b = locations[b]
            friend_travel_time[a][b] = travel_times_dict[(loc_a, loc_b)]

    travel_time_marina = [
        travel_times_dict[('Marina District', friends[0]['location'])],
        travel_times_dict[('Marina District', friends[1]['location'])],
        travel_times_dict[('Marina District', friends[2]['location'])],
        travel_times_dict[('Marina District', friends[3]['location'])],
        travel_times_dict[('Marina District', friends[4]['location'])],
        travel_times_dict[('Marina District', friends[5]['location'])],
        travel_times_dict[('Marina District', friends[6]['location'])],
        travel_times_dict[('Marina District', friends[7]['location'])],
        travel_times_dict[('Marina District', friends[8]['location'])],
    ]

    for N in range(9, 0, -1):
        solver = z3.Solver()
        friends_vars = [z3.Int(f'friend_{i}') for i in range(N)]
        for f in friends_vars:
            solver.add(z3.And(f >= 0, f <= 8))
        solver.add(z3.Distinct(friends_vars))
        start_times = [z3.Int(f'start_{i}') for i in range(N)]
        end_times = [z3.Int(f'end_{i}') for i in range(N)]
        for i in range(N):
            friend_idx = friends_vars[i]
            friend = friends[friend_idx]
            avail_start = friend['available_start']
            avail_end = friend['available_end']
            duration = friend['required_duration']
            if i == 0:
                tt_expr = 0
                for a in range(9):
                    tt_expr = z3.If(friend_idx == a, travel_time_marina[a], tt_expr)
                arrival_time = 540 + tt_expr
                solver.add(start_times[i] >= arrival_time)
            else:
                prev_idx = friends_vars[i-1]
                curr_idx = friends_vars[i]
                tt_expr = 0
                for a in range(9):
                    row_expr = 0
                    for b in range(9):
                        row_expr = z3.If(curr_idx == b, friend_travel_time[a][b], row_expr)
                    tt_expr = z3.If(prev_idx == a, row_expr, tt_expr)
                solver.add(start_times[i] >= end_times[i-1] + tt_expr)
            solver.add(start_times[i] >= avail_start)
            solver.add(start_times[i] <= avail_end - duration)
            solver.add(end_times[i] == start_times[i] + duration)
            solver.add(end_times[i] <= avail_end)
        if solver.check() == z3.sat:
            model = solver.model()
            itinerary = []
            for i in range(N):
                friend_idx = model.eval(friends_vars[i]).as_long()
                start = model.eval(start_times[i]).as_long()
                end = model.eval(end_times[i]).as_long()
                name = friends[friend_idx]['name']
                start_hh = start // 60
                start_mm = start % 60
                end_hh = end // 60
                end_mm = end % 60
                start_time_str = f"{start_hh:02d}:{start_mm:02d}"
                end_time_str = f"{end_hh:02d}:{end_mm:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time_str,
                    "end_time": end_time_str,
                })
            print(json.dumps({"itinerary": itinerary}))
            return
    print(json.dumps({"itinerary": []}))

solve()