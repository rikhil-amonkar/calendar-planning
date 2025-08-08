from z3 import *

def main():
    # Define the travel time dictionary
    travel_dict = {
        'Russian Hill': {
            'Russian Hill': 0,
            'Pacific Heights': 7,
            'North Beach': 5,
            'Golden Gate Park': 21,
            'Embarcadero': 8,
            'Haight-Ashbury': 17,
            "Fisherman's Wharf": 7,
            'Mission District': 16,
            'Alamo Square': 15,
            'Bayview': 23,
            'Richmond District': 14
        },
        'Pacific Heights': {
            'Russian Hill': 7,
            'Pacific Heights': 0,
            'North Beach': 9,
            'Golden Gate Park': 15,
            'Embarcadero': 10,
            'Haight-Ashbury': 11,
            "Fisherman's Wharf": 13,
            'Mission District': 15,
            'Alamo Square': 10,
            'Bayview': 22,
            'Richmond District': 12
        },
        'North Beach': {
            'Russian Hill': 4,
            'Pacific Heights': 8,
            'North Beach': 0,
            'Golden Gate Park': 22,
            'Embarcadero': 6,
            'Haight-Ashbury': 18,
            "Fisherman's Wharf": 5,
            'Mission District': 18,
            'Alamo Square': 16,
            'Bayview': 25,
            'Richmond District': 18
        },
        'Golden Gate Park': {
            'Russian Hill': 19,
            'Pacific Heights': 16,
            'North Beach': 23,
            'Golden Gate Park': 0,
            'Embarcadero': 25,
            'Haight-Ashbury': 7,
            "Fisherman's Wharf": 24,
            'Mission District': 17,
            'Alamo Square': 9,
            'Bayview': 23,
            'Richmond District': 7
        },
        'Embarcadero': {
            'Russian Hill': 8,
            'Pacific Heights': 11,
            'North Beach': 5,
            'Golden Gate Park': 25,
            'Embarcadero': 0,
            'Haight-Ashbury': 21,
            "Fisherman's Wharf": 6,
            'Mission District': 20,
            'Alamo Square': 19,
            'Bayview': 21,
            'Richmond District': 21
        },
        'Haight-Ashbury': {
            'Russian Hill': 17,
            'Pacific Heights': 12,
            'North Beach': 19,
            'Golden Gate Park': 7,
            'Embarcadero': 20,
            'Haight-Ashbury': 0,
            "Fisherman's Wharf": 23,
            'Mission District': 11,
            'Alamo Square': 5,
            'Bayview': 18,
            'Richmond District': 10
        },
        "Fisherman's Wharf": {
            'Russian Hill': 7,
            'Pacific Heights': 12,
            'North Beach': 6,
            'Golden Gate Park': 25,
            'Embarcadero': 8,
            'Haight-Ashbury': 22,
            "Fisherman's Wharf": 0,
            'Mission District': 22,
            'Alamo Square': 21,
            'Bayview': 26,
            'Richmond District': 18
        },
        'Mission District': {
            'Russian Hill': 15,
            'Pacific Heights': 16,
            'North Beach': 17,
            'Golden Gate Park': 17,
            'Embarcadero': 19,
            'Haight-Ashbury': 12,
            "Fisherman's Wharf": 22,
            'Mission District': 0,
            'Alamo Square': 11,
            'Bayview': 14,
            'Richmond District': 20
        },
        'Alamo Square': {
            'Russian Hill': 13,
            'Pacific Heights': 10,
            'North Beach': 15,
            'Golden Gate Park': 9,
            'Embarcadero': 16,
            'Haight-Ashbury': 5,
            "Fisherman's Wharf": 19,
            'Mission District': 10,
            'Alamo Square': 0,
            'Bayview': 16,
            'Richmond District': 11
        },
        'Bayview': {
            'Russian Hill': 23,
            'Pacific Heights': 23,
            'North Beach': 22,
            'Golden Gate Park': 22,
            'Embarcadero': 19,
            'Haight-Ashbury': 19,
            "Fisherman's Wharf": 25,
            'Mission District': 13,
            'Alamo Square': 16,
            'Bayview': 0,
            'Richmond District': 25
        },
        'Richmond District': {
            'Russian Hill': 13,
            'Pacific Heights': 10,
            'North Beach': 17,
            'Golden Gate Park': 9,
            'Embarcadero': 19,
            'Haight-Ashbury': 10,
            "Fisherman's Wharf": 18,
            'Mission District': 20,
            'Alamo Square': 13,
            'Bayview': 27,
            'Richmond District': 0
        }
    }

    # Define friends: (name, location, window_start, window_end, min_duration)
    friends = [
        ('Emily', 'Pacific Heights', 15, 285, 120),
        ('Helen', 'North Beach', 285, 585, 30),
        ('Kimberly', 'Golden Gate Park', 585, 735, 75),
        ('James', 'Embarcadero', 90, 150, 30),
        ('Linda', 'Haight-Ashbury', 0, 615, 15),
        ('Paul', "Fisherman's Wharf", 345, 585, 90),
        ('Anthony', 'Mission District', 0, 345, 105),
        ('Nancy', 'Alamo Square', 0, 285, 120),
        ('William', 'Bayview', 510, 690, 120),
        ('Margaret', 'Richmond District', 375, 435, 45)
    ]

    # Create Z3 variables
    n_friends = len(friends)
    met = [Bool(f'met_{i}') for i in range(n_friends)]
    S = [Int(f'S_{i}') for i in range(n_friends)]
    E = [Int(f'E_{i}') for i in range(n_friends)]

    # Virtual meeting: index = n_friends (i.e., 10)
    virtual_index = n_friends
    virtual_location = 'Russian Hill'
    all_locations = [f[1] for f in friends] + [virtual_location]

    # Create solver and add constraints
    opt = Optimize()
    
    # For each friend, if met, set the meeting constraints
    for i in range(n_friends):
        name, loc, start_win, end_win, min_dur = friends[i]
        opt.add(Implies(met[i], And(
            S[i] >= start_win,
            E[i] == S[i] + min_dur,
            E[i] <= end_win
        )))
    
    # For every pair of meetings (including virtual meeting), add disjunctive constraint
    for i in range(n_friends + 1):
        for j in range(i + 1, n_friends + 1):
            # Condition for i and j being met: for virtual meeting, it's always met
            cond_i = met[i] if i < n_friends else True
            cond_j = met[j] if j < n_friends else True
            both_met = And(cond_i, cond_j)
            
            loc_i = all_locations[i]
            loc_j = all_locations[j]
            
            # Get travel times
            travel_ji = travel_dict[loc_j][loc_i]  # from j to i
            travel_ij = travel_dict[loc_i][loc_j]  # from i to j
            
            # Get start and end times for i and j
            S_i = S[i] if i < n_friends else 0
            E_i = E[i] if i < n_friends else 0
            S_j = S[j] if j < n_friends else 0
            E_j = E[j] if j < n_friends else 0
            
            # Disjunctive constraint
            opt.add(Implies(both_met, Or(
                S_i >= E_j + travel_ji,
                S_j >= E_i + travel_ij
            )))
    
    # Maximize the number of friends met
    total_met = Sum([If(met_i, 1, 0) for met_i in met])
    opt.maximize(total_met)
    
    # Solve
    if opt.check() == sat:
        m = opt.model()
        scheduled_meetings = []
        for i in range(n_friends):
            if is_true(m[met[i]]):
                start_min = m[S[i]].as_long()
                end_min = m[E[i]].as_long()
                name = friends[i][0]
                # Convert minutes to time string (from 9:00 AM base)
                start_hour = 9 + start_min // 60
                start_minute = start_min % 60
                end_hour = 9 + end_min // 60
                end_minute = end_min % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                scheduled_meetings.append({
                    'person': name,
                    'start_time': start_str,
                    'end_time': end_str
                })
        # Sort by start time
        scheduled_meetings.sort(key=lambda x: x['start_time'])
        # Format as required
        result = {"itinerary": [{"action": "meet", "person": mt['person'], "start_time": mt['start_time'], "end_time": mt['end_time']} for mt in scheduled_meetings]}
        print(f"SOLUTION: {result}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()