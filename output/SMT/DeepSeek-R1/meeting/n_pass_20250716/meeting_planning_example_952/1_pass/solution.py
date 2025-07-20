from z3 import *

def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

locations = [
    'Bayview', 
    'North Beach', 
    "Fisherman's Wharf", 
    'Haight-Ashbury', 
    'Nob Hill', 
    'Golden Gate Park', 
    'Union Square', 
    'Alamo Square', 
    'Presidio', 
    'Chinatown', 
    'Pacific Heights'
]

travel_text = """Bayview to North Beach: 22.
Bayview to Fisherman's Wharf: 25.
Bayview to Haight-Ashbury: 19.
Bayview to Nob Hill: 20.
Bayview to Golden Gate Park: 22.
Bayview to Union Square: 18.
Bayview to Alamo Square: 16.
Bayview to Presidio: 32.
Bayview to Chinatown: 19.
Bayview to Pacific Heights: 23.
North Beach to Bayview: 25.
North Beach to Fisherman's Wharf: 5.
North Beach to Haight-Ashbury: 18.
North Beach to Nob Hill: 7.
North Beach to Golden Gate Park: 22.
North Beach to Union Square: 7.
North Beach to Alamo Square: 16.
North Beach to Presidio: 17.
North Beach to Chinatown: 6.
North Beach to Pacific Heights: 8.
Fisherman's Wharf to Bayview: 26.
Fisherman's Wharf to North Beach: 6.
Fisherman's Wharf to Haight-Ashbury: 22.
Fisherman's Wharf to Nob Hill: 11.
Fisherman's Wharf to Golden Gate Park: 25.
Fisherman's Wharf to Union Square: 13.
Fisherman's Wharf to Alamo Square: 21.
Fisherman's Wharf to Presidio: 17.
Fisherman's Wharf to Chinatown: 12.
Fisherman's Wharf to Pacific Heights: 12.
Haight-Ashbury to Bayview: 18.
Haight-Ashbury to North Beach: 19.
Haight-Ashbury to Fisherman's Wharf: 23.
Haight-Ashbury to Nob Hill: 15.
Haight-Ashbury to Golden Gate Park: 7.
Haight-Ashbury to Union Square: 19.
Haight-Ashbury to Alamo Square: 5.
Haight-Ashbury to Presidio: 15.
Haight-Ashbury to Chinatown: 19.
Haight-Ashbury to Pacific Heights: 12.
Nob Hill to Bayview: 19.
Nob Hill to North Beach: 8.
Nob Hill to Fisherman's Wharf: 10.
Nob Hill to Haight-Ashbury: 13.
Nob Hill to Golden Gate Park: 17.
Nob Hill to Union Square: 7.
Nob Hill to Alamo Square: 11.
Nob Hill to Presidio: 17.
Nob Hill to Chinatown: 6.
Nob Hill to Pacific Heights: 8.
Golden Gate Park to Bayview: 23.
Golden Gate Park to North Beach: 23.
Golden Gate Park to Fisherman's Wharf: 24.
Golden Gate Park to Haight-Ashbury: 7.
Golden Gate Park to Nob Hill: 20.
Golden Gate Park to Union Square: 22.
Golden Gate Park to Alamo Square: 9.
Golden Gate Park to Presidio: 11.
Golden Gate Park to Chinatown: 23.
Golden Gate Park to Pacific Heights: 16.
Union Square to Bayview: 15.
Union Square to North Beach: 10.
Union Square to Fisherman's Wharf: 15.
Union Square to Haight-Ashbury: 18.
Union Square to Nob Hill: 9.
Union Square to Golden Gate Park: 22.
Union Square to Alamo Square: 15.
Union Square to Presidio: 24.
Union Square to Chinatown: 7.
Union Square to Pacific Heights: 15.
Alamo Square to Bayview: 16.
Alamo Square to North Beach: 15.
Alamo Square to Fisherman's Wharf: 19.
Alamo Square to Haight-Ashbury: 5.
Alamo Square to Nob Hill: 11.
Alamo Square to Golden Gate Park: 9.
Alamo Square to Union Square: 14.
Alamo Square to Presidio: 17.
Alamo Square to Chinatown: 15.
Alamo Square to Pacific Heights: 10.
Presidio to Bayview: 31.
Presidio to North Beach: 18.
Presidio to Fisherman's Wharf: 19.
Presidio to Haight-Ashbury: 15.
Presidio to Nob Hill: 18.
Presidio to Golden Gate Park: 12.
Presidio to Union Square: 22.
Presidio to Alamo Square: 19.
Presidio to Chinatown: 21.
Presidio to Pacific Heights: 11.
Chinatown to Bayview: 20.
Chinatown to North Beach: 3.
Chinatown to Fisherman's Wharf: 8.
Chinatown to Haight-Ashbury: 19.
Chinatown to Nob Hill: 9.
Chinatown to Golden Gate Park: 23.
Chinatown to Union Square: 7.
Chinatown to Alamo Square: 17.
Chinatown to Presidio: 19.
Chinatown to Pacific Heights: 10.
Pacific Heights to Bayview: 22.
Pacific Heights to North Beach: 9.
Pacific Heights to Fisherman's Wharf: 13.
Pacific Heights to Haight-Ashbury: 11.
Pacific Heights to Nob Hill: 8.
Pacific Heights to Golden Gate Park: 15.
Pacific Heights to Union Square: 12.
Pacific Heights to Alamo Square: 10.
Pacific Heights to Presidio: 11.
Pacific Heights to Chinatown: 11."""

travel_dict = {}
for loc in locations:
    travel_dict[loc] = {}

lines = travel_text.strip().split('\n')
for line in lines:
    if not line.strip():
        continue
    parts = line.split(':')
    time_part = parts[1].strip()
    time_val = int(time_part.rstrip('.').strip())
    locs_part = parts[0].strip()
    locs = locs_part.split(' to ')
    from_loc = locs[0].strip()
    to_loc = locs[1].strip()
    if from_loc in travel_dict and to_loc in travel_dict[from_loc]:
        pass
    travel_dict[from_loc][to_loc] = time_val

friends = [
    ('Brian', 'North Beach', (13*60, 19*60), 90),
    ('Richard', "Fisherman's Wharf", (11*60, 12*60+45), 60),
    ('Ashley', 'Haight-Ashbury', (15*60, 20*60+30), 90),
    ('Elizabeth', 'Nob Hill', (11*60+45, 18*60+30), 75),
    ('Jessica', 'Golden Gate Park', (20*60, 21*60+45), 105),
    ('Deborah', 'Union Square', (17*60+30, 22*60), 60),
    ('Kimberly', 'Alamo Square', (17*60+30, 21*60+15), 45),
    ('Matthew', 'Presidio', (8*60+15, 9*60), 15),
    ('Kenneth', 'Chinatown', (13*60+45, 19*60+30), 105),
    ('Anthony', 'Pacific Heights', (14*60+15, 16*60), 30)
]

solver = Solver()
n = len(friends)

meet = [Bool(f'meet_{i}') for i in range(n)]
start = [Int(f'start_{i}') for i in range(n)]

for i in range(n):
    name, loc, (avail_start, avail_end), dur_req = friends[i]
    solver.add(Implies(meet[i], start[i] >= avail_start))
    solver.add(Implies(meet[i], start[i] + dur_req <= avail_end))
    solver.add(Implies(meet[i], start[i] >= 540 + travel_dict['Bayview'][loc]))

for i in range(n):
    for j in range(i+1, n):
        if i == j:
            continue
        name_i, loc_i, _, dur_i = friends[i]
        name_j, loc_j, _, dur_j = friends[j]
        travel_ij = travel_dict[loc_i][loc_j]
        travel_ji = travel_dict[loc_j][loc_i]
        c1 = (start[j] >= start[i] + dur_i + travel_ij)
        c2 = (start[i] >= start[j] + dur_j + travel_ji)
        solver.add(Implies(And(meet[i], meet[j]), Or(c1, c2)))

obj = Sum([If(meet[i], 1, 0) for i in range(n)])

opt = Optimize()
opt.add(solver.assertions())
opt.maximize(obj)

if opt.check() == sat:
    m = opt.model()
    total_met = 0
    schedule = []
    for i in range(n):
        if is_true(m.eval(meet[i])):
            total_met += 1
            name, loc, _, dur_req = friends[i]
            s_val = m.eval(start[i]).as_long()
            e_val = s_val + dur_req
            schedule.append((name, loc, s_val, e_val))
    schedule.sort(key=lambda x: x[2])
    print(f"Total friends met: {total_met}")
    for name, loc, s, e in schedule:
        print(f"Meet {name} at {loc} from {min_to_time(s)} to {min_to_time(e)}")
else:
    print("No solution found.")