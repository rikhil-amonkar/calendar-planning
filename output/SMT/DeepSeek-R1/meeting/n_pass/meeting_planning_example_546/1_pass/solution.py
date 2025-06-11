from z3 import *

# Travel times dictionary
travel_dict = {
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Bayview'): 21,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Bayview'): 26,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Bayview'): 15,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Bayview'): 19,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Bayview'): 22,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Bayview'): 19,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Nob Hill'): 20
}

# Friend data
friends = ['Kenneth', 'Lisa', 'Joshua', 'Nancy', 'Andrew', 'John']

locations = {
    'Kenneth': 'Richmond District',
    'Lisa': 'Union Square',
    'Joshua': 'Financial District',
    'Nancy': 'Pacific Heights',
    'Andrew': 'Nob Hill',
    'John': 'Bayview'
}

start_avail = {
    'Kenneth': 735,  # 9:15 PM (12 hours 15 minutes from 9:00 AM)
    'Lisa': 0,        # 9:00 AM
    'Joshua': 180,    # 12:00 PM
    'Nancy': 0,       # 9:00 AM
    'Andrew': 150,    # 11:30 AM
    'John': 465       # 4:45 PM
}

end_avail = {
    'Kenneth': 780,   # 10:00 PM
    'Lisa': 450,      # 4:30 PM
    'Joshua': 375,    # 3:15 PM
    'Nancy': 150,     # 11:30 AM
    'Andrew': 675,    # 8:15 PM
    'John': 750       # 9:30 PM
}

min_dur = {
    'Kenneth': 30,
    'Lisa': 45,
    'Joshua': 15,
    'Nancy': 90,
    'Andrew': 60,
    'John': 75
}

# Create Z3 variables and solver
s = Optimize()

meet = {f: Bool(f"meet_{f}") for f in friends}
start = {f: Int(f"start_{f}") for f in friends}

# Before matrix for ordering
before = {}
for i in friends:
    for j in friends:
        if i != j:
            before[(i, j)] = Bool(f"before_{i}_{j}")

# Constraints for each friend
for f in friends:
    # If meeting the friend, enforce time window and duration
    s.add(Implies(meet[f], And(
        start[f] >= start_avail[f],
        start[f] + min_dur[f] <= end_avail[f],
        start[f] >= 0
    )))
    # Constraint: start time at least travel time from Embarcadero
    travel_emb = travel_dict[('Embarcadero', locations[f])]
    s.add(Implies(meet[f], start[f] >= travel_emb))

# Constraints for each pair of distinct friends
for i in friends:
    for j in friends:
        if i == j:
            continue
        cond = And(meet[i], meet[j])
        # One must be before the other
        s.add(Implies(cond, Or(before[(i, j)], before[(j, i)])))
        s.add(Implies(cond, Not(And(before[(i, j)], before[(j, i)]))))
        # Travel time constraint if i is before j
        travel_ij = travel_dict[(locations[i], locations[j])]
        s.add(Implies(And(cond, before[(i, j)]), 
                      start[j] >= start[i] + min_dur[i] + travel_ij))

# Transitivity constraints
for i in friends:
    for j in friends:
        if i == j:
            continue
        for k in friends:
            if k == i or k == j:
                continue
            s.add(Implies(And(meet[i], meet[j], meet[k]),
                          Implies(And(before[(i, j)], before[(j, k)]), 
                                 before[(i, k)])))

# Maximize the number of friends met
s.maximize(Sum([If(meet[f], 1, 0) for f in friends]))

# Check and output the solution
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    total_met = 0
    schedule = []
    for f in friends:
        if m.evaluate(meet[f]):
            total_met += 1
            start_time = m.evaluate(start[f])
            if isinstance(start_time, IntNumRef):
                start_val = start_time.as_long()
            else:
                start_val = start_time
            # Convert start time to time string
            hours = 9 + start_val // 60
            minutes = start_val % 60
            am_pm = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            end_val = start_val + min_dur[f]
            end_hours = 9 + end_val // 60
            end_minutes = end_val % 60
            end_am_pm = "AM" if end_hours < 12 else "PM"
            if end_hours > 12:
                end_hours -= 12
            schedule.append((
                f, 
                f"{hours}:{minutes:02d} {am_pm}", 
                f"{end_hours}:{end_minutes:02d} {end_am_pm}"
            ))
    print(f"Total friends met: {total_met}")
    for entry in schedule:
        print(f"Meet {entry[0]} from {entry[1]} to {entry[2]}")
else:
    print("No solution found")