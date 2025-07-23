from z3 import *
import json

def time_to_minutes(time_tuple):
    return time_tuple[0] * 60 + time_tuple[1]

friends = [
    ("Steven", "North Beach", (17, 30), (20, 30), 15),
    ("Sarah", "Golden Gate Park", (17, 0), (19, 15), 75),
    ("Brian", "Embarcadero", (14, 15), (16, 0), 105),
    ("Stephanie", "Haight-Ashbury", (10, 15), (12, 15), 75),
    ("Melissa", "Richmond District", (14, 0), (19, 30), 30),
    ("Nancy", "Nob Hill", (8, 15), (12, 45), 90),
    ("David", "Marina District", (11, 15), (13, 15), 120),
    ("James", "Presidio", (15, 0), (18, 15), 120),
    ("Elizabeth", "Union Square", (11, 30), (21, 0), 60),
    ("Robert", "Financial District", (13, 15), (15, 15), 45)
]

travel_dict = {
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Financial District"): 21,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Financial District"): 8,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Financial District"): 26,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Financial District"): 22,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Financial District"): 9,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Financial District"): 17,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Financial District"): 23,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Financial District"): 9,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Union Square"): 9
}

n_meetings = 11
locations = ["The Castro"] + [f[1] for f in friends]

solver = Optimize()
solver.set("timeout", 300000)

active = [Bool(f'active_{i}') for i in range(n_meetings)]
solver.add(active[0] == True)

t = [Int(f't_{i}') for i in range(n_meetings)]
durations = [0] * n_meetings
end_time = [Int(f'end_{i}') for i in range(n_meetings)]

solver.add(t[0] == 540, end_time[0] == 540)

for i in range(1, n_meetings):
    name, loc, start_win, end_win, min_dur = friends[i-1]
    win_start = time_to_minutes(start_win)
    win_end = time_to_minutes(end_win)
    durations[i] = min_dur
    
    solver.add(Implies(active[i], 
                      And(t[i] >= win_start,
                          t[i] + min_dur <= win_end,
                          t[i] >= 0,
                          t[i] <= 1260)))
    solver.add(end_time[i] == t[i] + min_dur)

before = {}
for i in range(n_meetings):
    for j in range(i+1, n_meetings):
        before[(i, j)] = Bool(f'before_{i}_{j}')

for i in range(n_meetings):
    for j in range(i+1, n_meetings):
        travel_ij = travel_dict.get((locations[i], locations[j]), 100000)
        travel_ji = travel_dict.get((locations[j], locations[i]), 100000)
        
        c1 = Implies(And(active[i], active[j], before[(i, j)]),
                     t[j] >= end_time[i] + travel_ij)
        c2 = Implies(And(active[i], active[j], Not(before[(i, j)])),
                     t[i] >= end_time[j] + travel_ji)
        solver.add(c1, c2)

goal = Sum([If(active[i], 1, 0) for i in range(1, n_meetings)])
solver.maximize(goal)

if solver.check() == sat:
    m = solver.model()
    active_meetings = []
    for i in range(1, n_meetings):
        if is_true(m[active[i]]):
            start_val = m.evaluate(t[i])
            end_val = m.evaluate(end_time[i])
            if isinstance(start_val, IntNumRef) and isinstance(end_val, IntNumRef):
                start_min = start_val.as_long()
                end_min = end_val.as_long()
                start_str = f"{start_min//60:02d}:{start_min%60:02d}"
                end_str = f"{end_min//60:02d}:{end_min%60:02d}"
                active_meetings.append({
                    "person": friends[i-1][0],
                    "start": start_min,
                    "start_str": start_str,
                    "end_str": end_str
                })
    active_meetings.sort(key=lambda x: x["start"])
    itinerary = []
    for meet in active_meetings:
        itinerary.append({
            "action": "meet",
            "person": meet["person"],
            "start_time": meet["start_str"],
            "end_time": meet["end_str"]
        })
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("No solution found")