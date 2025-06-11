from z3 import *

def min_to_time(minutes_from_9am):
    total_minutes_from_midnight = 9*60 + minutes_from_9am
    hours = total_minutes_from_midnight // 60
    minutes = total_minutes_from_midnight % 60
    period = 'PM' if hours >= 12 else 'AM'
    hours12 = hours % 12
    if hours12 == 0:
        hours12 = 12
    return f"{hours12}:{minutes:02d}{period}"

def main():
    districts_in_order = [
        'Pacific Heights',
        'Marina District',
        'The Castro',
        'Richmond District',
        'Alamo Square',
        'Financial District',
        'Presidio',
        'Mission District',
        'Nob Hill',
        'Russian Hill'
    ]
    
    travel_times_list = [
        [6, 16, 12, 10, 13, 11, 15, 8, 7],
        [7, 22, 11, 15, 17, 10, 20, 12, 8],
        [16, 21, 16, 8, 21, 20, 7, 16, 18],
        [10, 9, 16, 13, 22, 7, 20, 17, 13],
        [10, 15, 8, 11, 17, 17, 10, 11, 13],
        [13, 15, 20, 21, 17, 22, 17, 8, 11],
        [11, 11, 21, 7, 19, 23, 26, 18, 14],
        [16, 19, 7, 20, 11, 15, 25, 12, 15],
        [8, 11, 17, 14, 11, 9, 17, 13, 5],
        [7, 7, 21, 14, 15, 11, 14, 16, 5]
    ]
    
    T = {}
    for d in districts_in_order:
        T[d] = {}
        
    for idx_from, from_district in enumerate(districts_in_order):
        times_row = travel_times_list[idx_from]
        idx = 0
        for idx_to, to_district in enumerate(districts_in_order):
            if from_district == to_district:
                T[from_district][to_district] = 0
            else:
                T[from_district][to_district] = times_row[idx]
                idx += 1
                
    friends = [
        # (name, location, available_start (min), available_end (min), duration (min))
        ('Linda', 'Marina District', 540, 780, 30),
        ('Kenneth', 'The Castro', 345, 435, 30),
        ('Kimberly', 'Richmond District', 315, 780, 30),
        ('Paul', 'Alamo Square', 720, 750, 15),
        ('Carol', 'Financial District', 75, 180, 60),
        ('Brian', 'Presidio', 60, 750, 75),
        ('Laura', 'Mission District', 435, 690, 30),
        ('Sandra', 'Nob Hill', 15, 570, 60),
        ('Karen', 'Russian Hill', 570, 780, 75)
    ]
    
    virtual = ('Virtual', 'Pacific Heights', 0, 0, 0)
    meetings = friends + [virtual]
    n_real = 9
    n_total = 10
    virtual_index = 9
    
    locs = [mtg[1] for mtg in meetings]
    travel_time = []
    for i in range(n_total):
        row = []
        for j in range(n_total):
            from_loc = locs[i]
            to_loc = locs[j]
            row.append(T[from_loc][to_loc])
        travel_time.append(row)
    
    m = [Bool('m%d' % i) for i in range(n_total)]
    a = [Int('a%d' % i) for i in range(n_total)]
    start_var = [Int('start%d' % i) for i in range(n_total)]
    p = [[Bool('p_%d_%d' % (j, i)) for i in range(n_total)] for j in range(n_total)]
    
    s = Solver()
    
    s.add(m[virtual_index] == True)
    s.add(a[virtual_index] == 0)
    s.add(start_var[virtual_index] == 0)
    
    for i in range(n_real):
        s.add(Implies(m[i], start_var[i] >= a[i]))
        s.add(Implies(m[i], start_var[i] >= meetings[i][2]))
        s.add(Implies(m[i], start_var[i] + meetings[i][4] <= meetings[i][3]))
        
        possible_js = [j for j in range(n_total) if j != i]
        s.add(Implies(m[i], Sum([If(p[j][i], 1, 0) for j in possible_js]) == 1))
        
        for j in possible_js:
            s.add(Implies(p[j][i], m[j]))
            s.add(Implies(p[j][i], a[i] >= a[j] + meetings[j][4] + travel_time[j][i]))
            s.add(Implies(Not(m[i]), Not(p[j][i])))
            
    for j in range(n_total):
        outgoing = [p[j][i] for i in range(n_total) if i != j]
        s.add(Sum([If(out, 1, 0) for out in outgoing]) <= 1)
        
    num_met = Sum([If(m[i], 1, 0) for i in range(n_real)])
    s.maximize(num_met)
    
    if s.check() == sat:
        model = s.model()
        met_count = 0
        for i in range(n_real):
            if model.evaluate(m[i]):
                met_count += 1
                st = model.evaluate(start_var[i])
                st_val = st.as_long() if isinstance(st, IntNumRef) else st
                start_str = min_to_time(st_val)
                end_val = st_val + meetings[i][4]
                end_str = min_to_time(end_val)
                print(f"Meet {friends[i][0]} at {friends[i][1]} from {start_str} to {end_str}")
        print(f"Total friends met: {met_count}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()