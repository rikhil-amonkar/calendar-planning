from z3 import *

# Hard-coded travel times dictionary
travel_times = {
    "Union Square": {
        "Mission District": 14,
        "Fisherman's Wharf": 15,
        "Russian Hill": 13,
        "Marina District": 18,
        "North Beach": 10,
        "Chinatown": 7,
        "Pacific Heights": 15,
        "The Castro": 17,
        "Nob Hill": 9,
        "Sunset District": 27
    },
    "Mission District": {
        "Union Square": 15,
        "Fisherman's Wharf": 22,
        "Russian Hill": 15,
        "Marina District": 19,
        "North Beach": 17,
        "Chinatown": 16,
        "Pacific Heights": 16,
        "The Castro": 7,
        "Nob Hill": 12,
        "Sunset District": 24
    },
    "Fisherman's Wharf": {
        "Union Square": 13,
        "Mission District": 22,
        "Russian Hill": 7,
        "Marina District": 9,
        "North Beach": 6,
        "Chinatown": 12,
        "Pacific Heights": 12,
        "The Castro": 27,
        "Nob Hill": 11,
        "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10,
        "Mission District": 16,
        "Fisherman's Wharf": 7,
        "Marina District": 7,
        "North Beach": 5,
        "Chinatown": 9,
        "Pacific Heights": 7,
        "The Castro": 21,
        "Nob Hill": 5,
        "Sunset District": 23
    },
    "Marina District": {
        "Union Square": 16,
        "Mission District": 20,
        "Fisherman's Wharf": 10,
        "Russian Hill": 8,
        "North Beach": 11,
        "Chinatown": 15,
        "Pacific Heights": 7,
        "The Castro": 22,
        "Nob Hill": 12,
        "Sunset District": 19
    },
    "North Beach": {
        "Union Square": 7,
        "Mission District": 18,
        "Fisherman's Wharf": 5,
        "Russian Hill": 4,
        "Marina District": 9,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 23,
        "Nob Hill": 7,
        "Sunset District": 27
    },
    "Chinatown": {
        "Union Square": 7,
        "Mission District": 17,
        "Fisherman's Wharf": 8,
        "Russian Hill": 7,
        "Marina District": 12,
        "North Beach": 3,
        "Pacific Heights": 10,
        "The Castro": 22,
        "Nob Hill": 9,
        "Sunset District": 29
    },
    "Pacific Heights": {
        "Union Square": 12,
        "Mission District": 15,
        "Fisherman's Wharf": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "North Beach": 9,
        "Chinatown": 11,
        "The Castro": 16,
        "Nob Hill": 8,
        "Sunset District": 21
    },
    "The Castro": {
        "Union Square": 19,
        "Mission District": 7,
        "Fisherman's Wharf": 24,
        "Russian Hill": 18,
        "Marina District": 21,
        "North Beach": 20,
        "Chinatown": 22,
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Sunset District": 17
    },
    "Nob Hill": {
        "Union Square": 7,
        "Mission District": 13,
        "Fisherman's Wharf": 10,
        "Russian Hill": 5,
        "Marina District": 11,
        "North Beach": 8,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 17,
        "Sunset District": 24
    },
    "Sunset District": {
        "Union Square": 30,
        "Mission District": 25,
        "Fisherman's Wharf": 29,
        "Russian Hill": 24,
        "Marina District": 21,
        "North Beach": 28,
        "Chinatown": 30,
        "Pacific Heights": 21,
        "The Castro": 17,
        "Nob Hill": 27
    }
}

# Friends data: (name, location, available_start (min since 9:00 AM), available_end, min_duration)
friends = [
    ("Kevin", "Mission District", 705, 765, 60),
    ("Mark", "Fisherman's Wharf", 495, 660, 90),
    ("Jessica", "Russian Hill", 0, 360, 120),
    ("Jason", "Marina District", 375, 765, 120),
    ("John", "North Beach", 45, 540, 15),
    ("Karen", "Chinatown", 465, 600, 75),
    ("Sarah", "Pacific Heights", 510, 555, 45),
    ("Amanda", "The Castro", 660, 735, 60),
    ("Nancy", "Nob Hill", 45, 240, 45),
    ("Rebecca", "Sunset District", 0, 360, 75)
]

n_real = 10
n = n_real + 1  # including dummy meeting

meet = [None] * n
start = [None] * n
end = [None] * n
loc = [None] * n

# Dummy meeting at Union Square (index n_real)
meet[n_real] = True
start[n_real] = 0
end[n_real] = 0
loc[n_real] = "Union Square"

# Real meetings (0 to n_real-1)
for i in range(n_real):
    meet[i] = Bool(f"meet_{i}")
    start[i] = Int(f"start_{i}")
    end[i] = Int(f"end_{i}")
    loc[i] = friends[i][1]

solver = Solver()

# Constraints for real meetings
for i in range(n_real):
    name, _, avail_start, avail_end, min_dur = friends[i]
    solver.add(If(meet[i],
                  And(start[i] >= avail_start,
                      end[i] == start[i] + min_dur,
                      end[i] <= avail_end),
                  True))

# Pairwise constraints for every pair (i, j) with i < j
for i in range(n):
    for j in range(i+1, n):
        # Condition: both meetings must be active
        if i == n_real:  # i is dummy
            cond = meet[j]
        elif j == n_real:  # j is dummy
            cond = meet[i]
        else:
            cond = And(meet[i], meet[j])
        
        time_ij = travel_times[loc[i]][loc[j]]
        time_ji = travel_times[loc[j]][loc[i]]
        
        solver.add(If(cond,
                       Or(end[i] + time_ij <= start[j],
                          end[j] + time_ji <= start[i]),
                       True))

# Objective: maximize number of meetings
objective = Sum([If(meet[i], 1, 0) for i in range(n_real)])

opt = Optimize()
opt.add(solver.assertions())
opt.maximize(objective)

if opt.check() == sat:
    m = opt.model()
    total_met = m.evaluate(objective)
    print(f"Total friends met: {total_met}")
    for i in range(n_real):
        if m.evaluate(meet[i]):
            s_val = m.evaluate(start[i])
            e_val = m.evaluate(end[i])
            s_min = s_val.as_long()
            e_min = e_val.as_long()
            s_hour = 9 + s_min // 60
            s_minute = s_min % 60
            e_hour = 9 + e_min // 60
            e_minute = e_min % 60
            print(f"Meet {friends[i][0]} at {friends[i][1]} from {s_hour}:{s_minute:02d} to {e_hour}:{e_minute:02d}")
        else:
            print(f"Cannot meet {friends[i][0]}")
else:
    print("No solution found")