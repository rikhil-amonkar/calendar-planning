from z3 import *

# Define travel times between districts
travel_time_dict = {
    "Marina District": {
        "Embarcadero": 14,
        "Bayview": 27,
        "Union Square": 16,
        "Chinatown": 15,
        "Sunset District": 19,
        "Golden Gate Park": 18,
        "Financial District": 17,
        "Haight-Ashbury": 16,
        "Mission District": 20
    },
    "Embarcadero": {
        "Marina District": 12,
        "Bayview": 21,
        "Union Square": 10,
        "Chinatown": 7,
        "Sunset District": 30,
        "Golden Gate Park": 25,
        "Financial District": 5,
        "Haight-Ashbury": 21,
        "Mission District": 20
    },
    "Bayview": {
        "Marina District": 27,
        "Embarcadero": 19,
        "Union Square": 18,
        "Chinatown": 19,
        "Sunset District": 23,
        "Golden Gate Park": 22,
        "Financial District": 19,
        "Haight-Ashbury": 19,
        "Mission District": 13
    },
    "Union Square": {
        "Marina District": 18,
        "Embarcadero": 11,
        "Bayview": 15,
        "Chinatown": 7,
        "Sunset District": 27,
        "Golden Gate Park": 22,
        "Financial District": 9,
        "Haight-Ashbury": 18,
        "Mission District": 14
    },
    "Chinatown": {
        "Marina District": 12,
        "Embarcadero": 5,
        "Bayview": 20,
        "Union Square": 7,
        "Sunset District": 29,
        "Golden Gate Park": 23,
        "Financial District": 5,
        "Haight-Ashbury": 19,
        "Mission District": 17
    },
    "Sunset District": {
        "Marina District": 21,
        "Embarcadero": 30,
        "Bayview": 22,
        "Union Square": 30,
        "Chinatown": 30,
        "Golden Gate Park": 11,
        "Financial District": 30,
        "Haight-Ashbury": 15,
        "Mission District": 25
    },
    "Golden Gate Park": {
        "Marina District": 16,
        "Embarcadero": 25,
        "Bayview": 23,
        "Union Square": 22,
        "Chinatown": 23,
        "Sunset District": 10,
        "Financial District": 26,
        "Haight-Ashbury": 7,
        "Mission District": 17
    },
    "Financial District": {
        "Marina District": 15,
        "Embarcadero": 4,
        "Bayview": 19,
        "Union Square": 9,
        "Chinatown": 5,
        "Sunset District": 30,
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Mission District": 17
    },
    "Haight-Ashbury": {
        "Marina District": 17,
        "Embarcadero": 20,
        "Bayview": 18,
        "Union Square": 19,
        "Chinatown": 19,
        "Sunset District": 15,
        "Golden Gate Park": 7,
        "Financial District": 21,
        "Mission District": 11
    },
    "Mission District": {
        "Marina District": 19,
        "Embarcadero": 19,
        "Bayview": 14,
        "Union Square": 15,
        "Chinatown": 16,
        "Sunset District": 24,
        "Golden Gate Park": 17,
        "Financial District": 15,
        "Haight-Ashbury": 12
    }
}

# Define friends' data: (index, name, location, window_start_min, window_end_min, min_time_min)
friends = [
    (0, "Joshua", "Embarcadero", 45, 540, 105),       # 9:45AM-6:00PM
    (1, "Jeffrey", "Bayview", 45, 675, 75),           # 9:45AM-8:15PM
    (2, "Charles", "Union Square", 105, 675, 120),    # 10:45AM-8:15PM
    (3, "Joseph", "Chinatown", 0, 390, 60),           # 9:00AM-3:30PM (effective from 9:00AM)
    (4, "Elizabeth", "Sunset District", 0, 45, 45),   # 9:00AM-9:45AM
    (5, "Matthew", "Golden Gate Park", 120, 630, 45), # 11:00AM-7:30PM
    (6, "Carol", "Financial District", 105, 135, 15), # 10:45AM-11:15AM
    (7, "Paul", "Haight-Ashbury", 615, 690, 15),      # 7:15PM-8:30PM
    (8, "Rebecca", "Mission District", 480, 765, 45)  # 5:00PM-9:45PM
]

# Precompute travel times from Marina to each friend's location
travel_from_marina = [ 
    travel_time_dict["Marina District"][friends[i][2]] for i in range(9)
]

# Precompute travel times between friends
travel_between = {}
for i in range(9):
    for j in range(9):
        if i != j:
            loc_i = friends[i][2]
            loc_j = friends[j][2]
            travel_between[(i, j)] = travel_time_dict[loc_i][loc_j]

# Initialize Z3 solver and variables
opt = Optimize()

# Sequence: 9 slots, each can be -1 (unused) or a meeting index (0-8)
seq = [ Int(f'seq_{k}') for k in range(9) ]

# Included: Boolean for each friend
included = [ Bool(f'included_{i}') for i in range(9) ]

# Start and end times (in minutes from 9:00 AM)
start = [ Int(f'start_{i}') for i in range(9) ]
end = [ Int(f'end_{i}') for i in range(9) ]

# Constraints for sequence and inclusion
for k in range(9):
    opt.add( Or(seq[k] == -1, And(seq[k] >= 0, seq[k] <= 8)) )

for i in range(9):
    opt.add( included[i] == Or([ seq[k] == i for k in range(9) ]) )

for k1 in range(9):
    for k2 in range(k1+1, 9):
        opt.add( If(And(seq[k1] != -1, seq[k2] != -1), seq[k1] != seq[k2], True) )

for k in range(8):
    opt.add( If(seq[k] == -1, seq[k+1] == -1, True) )

# Constraints for meeting times and durations
for i in range(9):
    window_start = friends[i][3]
    window_end = friends[i][4]
    min_time = friends[i][5]
    opt.add( If(included[i], 
               And( end[i] == start[i] + min_time,
                    start[i] >= window_start,
                    end[i] <= window_end ),
               True ) )

# Constraints for travel times
# First meeting: from Marina to the first friend's location
for i in range(9):
    opt.add( If(And(seq[0] != -1, seq[0] == i),
                start[i] >= travel_from_marina[i],
                True) )

# Subsequent meetings: travel from previous to current
for k in range(1, 9):
    for i in range(9):
        for j in range(9):
            if i != j:
                opt.add( If(And(seq[k-1] == i, seq[k] == j, seq[k] != -1),
                            start[j] >= end[i] + travel_between[(i, j)],
                            True) )

# Maximize the number of included meetings
total_meetings = Sum([ If(included[i], 1, 0) for i in range(9) ])
opt.maximize(total_meetings)

# Solve the model
if opt.check() == sat:
    m = opt.model()
    schedule = []
    for i in range(9):
        if is_true(m.eval(included[i])):
            s_val = m.eval(start[i])
            e_val = m.eval(end[i])
            try:
                s_minutes = s_val.as_long()
                e_minutes = e_val.as_long()
            except:
                s_minutes = int(str(s_val))
                e_minutes = int(str(e_val))
            start_hour = 9 + s_minutes // 60
            start_minute = s_minutes % 60
            end_hour = 9 + e_minutes // 60
            end_minute = e_minutes % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            schedule.append( (start_str, end_str, friends[i][1]) )
    schedule.sort(key=lambda x: x[0])
    itinerary = [ {"action": "meet", "person": name, "start_time": s, "end_time": e} for s, e, name in schedule ]
    print('SOLUTION:')
    print({"itinerary": itinerary})
else:
    print("SOLUTION:")
    print('{"itinerary": []}')