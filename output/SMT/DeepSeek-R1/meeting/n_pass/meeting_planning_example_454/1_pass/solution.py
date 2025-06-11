from z3 import *

def min_to_time_str(minutes):
    total_minutes = 9 * 60 + minutes
    hours = total_minutes // 60
    mins = total_minutes % 60
    return f"{hours}:{mins:02d}"

travel = [
    [0, 12, 31, 21, 18, 26],
    [11, 0, 23, 23, 24, 17],
    [31, 22, 0, 18, 21, 13],
    [19, 23, 22, 0, 3, 18],
    [17, 22, 22, 6, 0, 18],
    [25, 17, 15, 16, 17, 0]
]

avail_start = [0, 285, 495, 0, 255, 0]
avail_end = [0, 360, 660, 345, 675, 135]
durations = [0, 30, 105, 90, 15, 105]

names = {
    1: "Jessica at Golden Gate Park",
    2: "Ashley at Bayview",
    3: "Ronald at Chinatown",
    4: "William at North Beach",
    5: "Daniel at Mission District"
}

s = Optimize()

meet = [None] * 6
s_time = [None] * 6
e_time = [None] * 6

meet[0] = BoolVal(True)
s_time[0] = 0
e_time[0] = 0

for i in range(1, 6):
    meet[i] = Bool(f'meet_{i}')
    s_time[i] = Int(f's_{i}')
    e_time[i] = Int(f'e_{i}')

for i in range(1, 6):
    s.add(Implies(meet[i], s_time[i] >= avail_start[i]))
    s.add(Implies(meet[i], e_time[i] <= avail_end[i]))
    s.add(Implies(meet[i], e_time[i] == s_time[i] + durations[i]))

for i in range(6):
    for j in range(6):
        if i == j:
            continue
        cond_i = meet[i] if i != 0 else BoolVal(True)
        cond_j = meet[j] if j != 0 else BoolVal(True)
        constraint = Or(
            s_time[i] >= e_time[j] + travel[j][i],
            s_time[j] >= e_time[i] + travel[i][j]
        )
        s.add(Implies(And(cond_i, cond_j), constraint))

total_meet = Sum([If(meet[i], 1, 0) for i in range(1, 6)])
s.maximize(total_meet)

if s.check() == sat:
    m = s.model()
    total_val = m.eval(total_meet)
    print("SOLUTION:")
    print(f"Total meetings: {total_val}")
    for i in range(1, 6):
        if is_true(m.eval(meet[i])):
            start_val = m.eval(s_time[i]).as_long()
            end_val = m.eval(e_time[i]).as_long()
            start_time = min_to_time_str(start_val)
            end_time = min_to_time_str(end_val)
            print(f"Meet {names[i]}: from {start_time} to {end_time}")
        else:
            print(f"Did not meet {names[i]}")
else:
    print("No solution found")