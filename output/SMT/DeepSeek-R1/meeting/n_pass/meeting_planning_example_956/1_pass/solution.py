from z3 import *

def main():
    # Define location names
    location_names = [
        'The Castro',
        'Alamo Square',
        'Richmond District',
        'Financial District',
        'Union Square',
        'Fisherman\'s Wharf',
        'Marina District',
        'Haight-Ashbury',
        'Mission District',
        'Pacific Heights',
        'Golden Gate Park'
    ]
    
    # Travel times data as a multi-line string
    travel_text = """
The Castro to Alamo Square: 8
The Castro to Richmond District: 16
The Castro to Financial District: 21
The Castro to Union Square: 19
The Castro to Fisherman's Wharf: 24
The Castro to Marina District: 21
The Castro to Haight-Ashbury: 6
The Castro to Mission District: 7
The Castro to Pacific Heights: 16
The Castro to Golden Gate Park: 11
Alamo Square to The Castro: 8
Alamo Square to Richmond District: 11
Alamo Square to Financial District: 17
Alamo Square to Union Square: 14
Alamo Square to Fisherman's Wharf: 19
Alamo Square to Marina District: 15
Alamo Square to Haight-Ashbury: 5
Alamo Square to Mission District: 10
Alamo Square to Pacific Heights: 10
Alamo Square to Golden Gate Park: 9
Richmond District to The Castro: 16
Richmond District to Alamo Square: 13
Richmond District to Financial District: 22
Richmond District to Union Square: 21
Richmond District to Fisherman's Wharf: 18
Richmond District to Marina District: 9
Richmond District to Haight-Ashbury: 10
Richmond District to Mission District: 20
Richmond District to Pacific Heights: 10
Richmond District to Golden Gate Park: 9
Financial District to The Castro: 20
Financial District to Alamo Square: 17
Financial District to Richmond District: 21
Financial District to Union Square: 9
Financial District to Fisherman's Wharf: 10
Financial District to Marina District: 15
Financial District to Haight-Ashbury: 19
Financial District to Mission District: 17
Financial District to Pacific Heights: 13
Financial District to Golden Gate Park: 23
Union Square to The Castro: 17
Union Square to Alamo Square: 15
Union Square to Richmond District: 20
Union Square to Financial District: 9
Union Square to Fisherman's Wharf: 15
Union Square to Marina District: 18
Union Square to Haight-Ashbury: 18
Union Square to Mission District: 14
Union Square to Pacific Heights: 15
Union Square to Golden Gate Park: 22
Fisherman's Wharf to The Castro: 27
Fisherman's Wharf to Alamo Square: 21
Fisherman's Wharf to Richmond District: 18
Fisherman's Wharf to Financial District: 11
Fisherman's Wharf to Union Square: 13
Fisherman's Wharf to Marina District: 9
Fisherman's Wharf to Haight-Ashbury: 22
Fisherman's Wharf to Mission District: 22
Fisherman's Wharf to Pacific Heights: 12
Fisherman's Wharf to Golden Gate Park: 25
Marina District to The Castro: 22
Marina District to Alamo Square: 15
Marina District to Richmond District: 11
Marina District to Financial District: 17
Marina District to Union Square: 16
Marina District to Fisherman's Wharf: 10
Marina District to Haight-Ashbury: 16
Marina District to Mission District: 20
Marina District to Pacific Heights: 7
Marina District to Golden Gate Park: 18
Haight-Ashbury to The Castro: 6
Haight-Ashbury to Alamo Square: 5
Haight-Ashbury to Richmond District: 10
Haight-Ashbury to Financial District: 21
Haight-Ashbury to Union Square: 19
Haight-Ashbury to Fisherman's Wharf: 23
Haight-Ashbury to Marina District: 17
Haight-Ashbury to Mission District: 11
Haight-Ashbury to Pacific Heights: 12
Haight-Ashbury to Golden Gate Park: 7
Mission District to The Castro: 7
Mission District to Alamo Square: 11
Mission District to Richmond District: 20
Mission District to Financial District: 15
Mission District to Union Square: 15
Mission District to Fisherman's Wharf: 22
Mission District to Marina District: 19
Mission District to Haight-Ashbury: 12
Mission District to Pacific Heights: 16
Mission District to Golden Gate Park: 17
Pacific Heights to The Castro: 16
Pacific Heights to Alamo Square: 10
Pacific Heights to Richmond District: 12
Pacific Heights to Financial District: 13
Pacific Heights to Union Square: 12
Pacific Heights to Fisherman's Wharf: 13
Pacific Heights to Marina District: 6
Pacific Heights to Haight-Ashbury: 11
Pacific Heights to Mission District: 15
Pacific Heights to Golden Gate Park: 15
Golden Gate Park to The Castro: 13
Golden Gate Park to Alamo Square: 9
Golden Gate Park to Richmond District: 7
Golden Gate Park to Financial District: 26
Golden Gate Park to Union Square: 22
Golden Gate Park to Fisherman's Wharf: 24
Golden Gate Park to Marina District: 16
Golden Gate Park to Haight-Ashbury: 7
Golden Gate Park to Mission District: 17
Golden Gate Park to Pacific Heights: 16
"""
    # Parse travel_text into a dictionary
    travel_dict = {}
    lines = travel_text.strip().split('\n')
    for line in lines:
        line = line.strip()
        if line == '':
            continue
        parts = line.split(':')
        if len(parts) < 2:
            continue
        route_str = parts[0].strip()
        time_str = parts[1].strip().rstrip('.')
        try:
            time_val = int(time_str)
        except:
            continue
        if ' to ' not in route_str:
            continue
        from_loc, to_loc = route_str.split(' to ')
        from_loc = from_loc.strip()
        to_loc = to_loc.strip()
        travel_dict[(from_loc, to_loc)] = time_val

    # Build travel time matrix T (11x11)
    T = [[0]*11 for _ in range(11)]
    for i in range(11):
        for j in range(11):
            loc_i = location_names[i]
            loc_j = location_names[j]
            if (loc_i, loc_j) in travel_dict:
                T[i][j] = travel_dict[(loc_i, loc_j)]
            elif (loc_j, loc_i) in travel_dict:
                T[i][j] = travel_dict[(loc_j, loc_i)]
            else:
                if i == j:
                    T[i][j] = 0
                else:
                    # This should not happen as we have all pairs
                    T[i][j] = 10000  # large penalty, but we have all pairs

    # Define friends data: (name, location, min_duration, (available_start, available_end) in minutes from 9:00 AM)
    friends = [
        ('William', 'Alamo Square', 60, (375, 495)),   # 3:15PM to 5:15PM
        ('Joshua', 'Richmond District', 15, (0, 660)),  # 7:00AM to 8:00PM
        ('Joseph', 'Financial District', 15, (135, 270)), # 11:15AM to 1:30PM
        ('David', 'Union Square', 45, (465, 615)),      # 4:45PM to 7:15PM
        ('Brian', 'Fisherman\'s Wharf', 105, (285, 705)), # 1:45PM to 8:45PM
        ('Karen', 'Marina District', 15, (150, 570)),   # 11:30AM to 6:30PM
        ('Anthony', 'Haight-Ashbury', 30, (0, 90)),     # 7:15AM to 10:30AM
        ('Matthew', 'Mission District', 120, (495, 615)), # 5:15PM to 7:15PM
        ('Helen', 'Pacific Heights', 75, (0, 180)),     # 8:00AM to 12:00PM
        ('Jeffrey', 'Golden Gate Park', 60, (600, 750))  # 7:00PM to 9:30PM
    ]

    # Map friend locations to indices
    loc_event = [0] * 11  # event0 (start) is The Castro -> index0
    for i in range(1, 11):
        # Friend for event i is friends[i-1]
        loc_name = friends[i-1][1]
        # Find the index of loc_name in location_names
        idx = location_names.index(loc_name)
        loc_event[i] = idx

    # D: min_duration for each event: event0 (start) has 0, event1..10 have the min_duration of the friend
    D = [0] * 11
    for i in range(1, 11):
        D[i] = friends[i-1][2]

    # Create solver
    s = Solver()

    # Meet variables for 10 friends (index0 to 9)
    meet = [Bool(f'meet_{i}') for i in range(10)]
    
    # Time variables: t0 (start) and t1..t10 for friends
    t = [Real(f't_{i}') for i in range(11)]
    
    # x[i][j]: for i in [0,10] and j in [1,10] (j is event index of friend event), i != j
    # We store for each i, a list for j from 1 to 10 (so 10 elements). The index in the list: j_index = j-1 (0-indexed)
    x = []
    for i in range(11):
        row = []
        for j in range(1, 11):
            if i == j:
                row.append(None)  # no variable for self-loop
            else:
                row.append(Bool(f'x_{i}_{j}'))
        x.append(row)

    # Constraint 1: t0 = 0 (start at 9:00AM)
    s.add(t[0] == 0)

    # Constraint 2: Time window for each friend event j (event index j from 1 to 10)
    for j in range(1, 11):
        fidx = j-1  # friend index in friends list
        start_win, end_win = friends[fidx][3]
        min_dur = friends[fidx][2]
        # If we meet this friend, then the meeting must be within [start_win, end_win - min_dur] for start time
        s.add(If(meet[fidx], And(t[j] >= start_win, t[j] + min_dur <= end_win), True)

    # Constraint 3: Graph constraints
    N = Sum([If(meet_i, 1, 0) for meet_i in meet])  # total number of meetings

    # Start out: from event0 (start) to event j (j=1..10)
    start_out = Sum([x[0][j] for j in range(0,10)])  # x[0][j] for j in 0..9 (which corresponds to event j+1)

    # If N>0, then start_out must be 1, else 0
    s.add(start_out == If(N > 0, 1, 0))

    # For each friend event j (event index j from 1 to 10)
    for j in range(1, 11):
        fidx = j-1
        # in_degree_j = sum_{i in [0,10] and i != j} x[i][j-1]  (because x[i] stores j in 0..9 for event1..10)
        in_degree_j = Sum([x[i][j-1] for i in range(0,11) if i != j])
        s.add(in_degree_j == meet[fidx])

    # For each friend event j, out_degree_j = sum_{k in [1,10] and k != j} x[j][k-1]
    for j in range(1, 11):
        fidx = j-1
        out_degree_j = Sum([x[j][k-1] for k in range(1,11) if k != j])
        s.add(out_degree_j <= meet[fidx])

    # Total edges: start_out + sum_{j=1 to 10} out_degree_j = N
    total_edges = start_out + Sum([Sum([x[j][k-1] for k in range(1,11) if k != j]) for j in range(1,11)])
    s.add(total_edges == N)

    # Time constraints for edges: if x[i][j-1] is True, then t[j] >= t[i] + D[i] + T[loc_event[i]][loc_event[j]]
    for i in range(0, 11):
        for j in range(1, 11):
            if i == j:
                continue
            # x[i][j-1] is the variable for edge from event i to event j
            travel_time = T[loc_event[i]][loc_event[j]]
            s.add(If(x[i][j-1], t[j] >= t[i] + D[i] + travel_time, True))

    # Set objective: maximize N
    s.maximize(N)

    # Solve
    result = s.check()
    if result == sat:
        m = s.model()
        n_val = m.eval(N)
        print(f"SOLUTION: Meet {n_val} friends")
        # Print the schedule
        for j in range(1, 11):
            fidx = j-1
            if is_true(m[meet[fidx]]):
                start_val = m[t[j]]
                # Convert start_val to a float
                if is_rational_value(start_val):
                    start_min = float(start_val.as_fraction())
                elif is_algebraic_value(start_val):
                    start_min = start_val.approx(10).as_fraction()
                else:
                    start_min = 0.0
                total_minutes = int(round(start_min))
                hours = total_minutes // 60
                minutes = total_minutes % 60
                base_hour = 9 + hours
                hour = base_hour
                am_pm = "AM"
                if hour >= 12:
                    am_pm = "PM"
                    if hour > 12:
                        hour -= 12
                elif hour == 0:
                    hour = 12
                print(f"Meet {friends[fidx][0]} at {friends[fidx][1]} starting at {hour}:{minutes:02d} {am_pm} for {friends[fidx][2]} minutes")
        # Print the travel path
        path = ["The Castro (start)"]
        current = 0
        visited = set([0])
        # Find the first from start
        next_evt = None
        for j in range(1, 11):
            if is_true(m[meet[j-1]]) and is_true(m[x[0][j-1]]):
                next_evt = j
                break
        while next_evt is not None and next_evt not in visited:
            visited.add(next_evt)
            path.append(f"{location_names[loc_event[next_evt]]} (meet {friends[next_evt-1][0]})")
            current = next_evt
            next_evt = None
            for k in range(1, 11):
                if k == current:
                    continue
                if is_true(m[meet[k-1]]) and is_true(m[x[current][k-1]]):
                    next_evt = k
                    break
        print("Travel path: " + " -> ".join(path))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()