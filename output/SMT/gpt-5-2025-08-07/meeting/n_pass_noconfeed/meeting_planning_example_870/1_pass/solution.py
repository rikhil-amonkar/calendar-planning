import json
from z3 import *

def minutes(tstr):
    # tstr like '9:00' or '13:30'
    h, m = map(int, tstr.split(':'))
    return h*60 + m

def fmt(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times in minutes (directed)
travel = {
    ('Pacific Heights','Marina District'): 6,
    ('Pacific Heights','The Castro'): 16,
    ('Pacific Heights','Richmond District'): 12,
    ('Pacific Heights','Alamo Square'): 10,
    ('Pacific Heights','Financial District'): 13,
    ('Pacific Heights','Presidio'): 11,
    ('Pacific Heights','Mission District'): 15,
    ('Pacific Heights','Nob Hill'): 8,
    ('Pacific Heights','Russian Hill'): 7,

    ('Marina District','Pacific Heights'): 7,
    ('Marina District','The Castro'): 22,
    ('Marina District','Richmond District'): 11,
    ('Marina District','Alamo Square'): 15,
    ('Marina District','Financial District'): 17,
    ('Marina District','Presidio'): 10,
    ('Marina District','Mission District'): 20,
    ('Marina District','Nob Hill'): 12,
    ('Marina District','Russian Hill'): 8,

    ('The Castro','Pacific Heights'): 16,
    ('The Castro','Marina District'): 21,
    ('The Castro','Richmond District'): 16,
    ('The Castro','Alamo Square'): 8,
    ('The Castro','Financial District'): 21,
    ('The Castro','Presidio'): 20,
    ('The Castro','Mission District'): 7,
    ('The Castro','Nob Hill'): 16,
    ('The Castro','Russian Hill'): 18,

    ('Richmond District','Pacific Heights'): 10,
    ('Richmond District','Marina District'): 9,
    ('Richmond District','The Castro'): 16,
    ('Richmond District','Alamo Square'): 13,
    ('Richmond District','Financial District'): 22,
    ('Richmond District','Presidio'): 7,
    ('Richmond District','Mission District'): 20,
    ('Richmond District','Nob Hill'): 17,
    ('Richmond District','Russian Hill'): 13,

    ('Alamo Square','Pacific Heights'): 10,
    ('Alamo Square','Marina District'): 15,
    ('Alamo Square','The Castro'): 8,
    ('Alamo Square','Richmond District'): 11,
    ('Alamo Square','Financial District'): 17,
    ('Alamo Square','Presidio'): 17,
    ('Alamo Square','Mission District'): 10,
    ('Alamo Square','Nob Hill'): 11,
    ('Alamo Square','Russian Hill'): 13,

    ('Financial District','Pacific Heights'): 13,
    ('Financial District','Marina District'): 15,
    ('Financial District','The Castro'): 20,
    ('Financial District','Richmond District'): 21,
    ('Financial District','Alamo Square'): 17,
    ('Financial District','Presidio'): 22,
    ('Financial District','Mission District'): 17,
    ('Financial District','Nob Hill'): 8,
    ('Financial District','Russian Hill'): 11,

    ('Presidio','Pacific Heights'): 11,
    ('Presidio','Marina District'): 11,
    ('Presidio','The Castro'): 21,
    ('Presidio','Richmond District'): 7,
    ('Presidio','Alamo Square'): 19,
    ('Presidio','Financial District'): 23,
    ('Presidio','Mission District'): 26,
    ('Presidio','Nob Hill'): 18,
    ('Presidio','Russian Hill'): 14,

    ('Mission District','Pacific Heights'): 16,
    ('Mission District','Marina District'): 19,
    ('Mission District','The Castro'): 7,
    ('Mission District','Richmond District'): 20,
    ('Mission District','Alamo Square'): 11,
    ('Mission District','Financial District'): 15,
    ('Mission District','Presidio'): 25,
    ('Mission District','Nob Hill'): 12,
    ('Mission District','Russian Hill'): 15,

    ('Nob Hill','Pacific Heights'): 8,
    ('Nob Hill','Marina District'): 11,
    ('Nob Hill','The Castro'): 17,
    ('Nob Hill','Richmond District'): 14,
    ('Nob Hill','Alamo Square'): 11,
    ('Nob Hill','Financial District'): 9,
    ('Nob Hill','Presidio'): 17,
    ('Nob Hill','Mission District'): 13,
    ('Nob Hill','Russian Hill'): 5,

    ('Russian Hill','Pacific Heights'): 7,
    ('Russian Hill','Marina District'): 7,
    ('Russian Hill','The Castro'): 21,
    ('Russian Hill','Richmond District'): 14,
    ('Russian Hill','Alamo Square'): 15,
    ('Russian Hill','Financial District'): 11,
    ('Russian Hill','Presidio'): 14,
    ('Russian Hill','Mission District'): 16,
    ('Russian Hill','Nob Hill'): 5,
}

def travel_time(a, b):
    return travel[(a, b)]

start_location = 'Pacific Heights'
start_time = minutes('9:00')

# Friends: name, location, window_start, window_end, min_duration
friends = [
    {'name': 'Linda',   'location': 'Marina District',   'start': minutes('18:00'), 'end': minutes('22:00'), 'duration': 30},
    {'name': 'Kenneth', 'location': 'The Castro',        'start': minutes('14:45'), 'end': minutes('16:15'), 'duration': 30},
    {'name': 'Kimberly','location': 'Richmond District', 'start': minutes('14:15'), 'end': minutes('22:00'), 'duration': 30},
    {'name': 'Paul',    'location': 'Alamo Square',      'start': minutes('21:00'), 'end': minutes('21:30'), 'duration': 15},
    {'name': 'Carol',   'location': 'Financial District','start': minutes('10:15'), 'end': minutes('12:00'), 'duration': 60},
    {'name': 'Brian',   'location': 'Presidio',          'start': minutes('10:00'), 'end': minutes('21:30'), 'duration': 75},
    {'name': 'Laura',   'location': 'Mission District',  'start': minutes('16:15'), 'end': minutes('20:30'), 'duration': 30},
    {'name': 'Sandra',  'location': 'Nob Hill',          'start': minutes('9:15'),  'end': minutes('18:30'), 'duration': 60},
    {'name': 'Karen',   'location': 'Russian Hill',      'start': minutes('18:30'), 'end': minutes('22:00'), 'duration': 75},
]

# Z3 variables
opt = Optimize()

start_vars = {}
meet_vars = {}
durations = {}

for f in friends:
    key = f['name']
    start_vars[key] = Int(f"start_{key}")
    meet_vars[key] = Bool(f"meet_{key}")
    durations[key] = f['duration']
    # Bound starts within reasonable day range
    opt.add(start_vars[key] >= 0, start_vars[key] <= 24*60)
    # If meeting, it must be within window and last for min duration
    opt.add(Implies(meet_vars[key],
                    And(start_vars[key] >= f['start'],
                        start_vars[key] + f['duration'] <= f['end'])))
    # From starting point to first meeting
    opt.add(Implies(meet_vars[key],
                    start_vars[key] >= start_time + travel_time(start_location, f['location'])))

# Non-overlap and travel time between meetings
n = len(friends)
for i in range(n):
    for j in range(i+1, n):
        fi = friends[i]
        fj = friends[j]
        si = start_vars[fi['name']]
        sj = start_vars[fj['name']]
        di = durations[fi['name']]
        dj = durations[fj['name']]
        ti_to_j = travel_time(fi['location'], fj['location'])
        tj_to_i = travel_time(fj['location'], fi['location'])
        opt.add(Implies(And(meet_vars[fi['name']], meet_vars[fj['name']]),
                        Or(
                            sj >= si + di + ti_to_j,
                            si >= sj + dj + tj_to_i
                        )))

# Objective: maximize number of friends met
total_met = Sum([If(meet_vars[f['name']], 1, 0) for f in friends])
opt.maximize(total_met)

# As a secondary objective, minimize the latest end time to prefer earlier schedules (optional)
latest_end = Int("latest_end")
opt.add(latest_end >= 0, latest_end <= 24*60)
for f in friends:
    opt.add(Implies(meet_vars[f['name']], latest_end >= start_vars[f['name']] + f['duration']))
opt.minimize(latest_end)

if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    itinerary = []
    for f in friends:
        name = f['name']
        if m.evaluate(meet_vars[name], model_completion=True) == True:
            s = m.evaluate(start_vars[name], model_completion=True).as_long()
            d = durations[name]
            entry = {
                "action": "meet",
                "location": f['location'],
                "person": name,
                "start_time": fmt(s),
                "end_time": fmt(s + d)
            }
            itinerary.append(entry)
    itinerary.sort(key=lambda x: minutes(x["start_time"]))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))