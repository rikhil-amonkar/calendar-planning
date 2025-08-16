from z3 import *
import json

def to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours:02d}:{minutes:02d}"

# First sequence: Karen -> Anthony -> Betty
s_k = Int('s_k')
s_a = Int('s_a')
s_b = Int('s_b')
e_k = s_k + 30
e_a = s_a + 105
e_b = s_b + 15

constraints = [
    # Karen's meeting
    s_k >= 565,  # arrival at Fisherman's from Bayview (25 min)
    e_k <= 900,  # ends by 3 PM

    # Anthony's meeting
    s_a >= e_k + 11,  # travel time from Fisherman's to FD is 11 min
    s_a >= 555,  # Anthony's earliest start (9:15 AM)
    s_a <= 1185,  # Anthony's latest start (7:45 PM)

    # Betty's meeting
    s_b >= e_a + 4,  # travel time from FD to Embarcadero is 4 min
    s_b >= 1185,  # Betty's earliest start (7:45 PM)
    s_b <= 1275,  # Betty's latest start (9:30 PM)
]

solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    sk_val = model[s_k].as_long()
    sa_val = model[s_a].as_long()
    sb_val = model[s_b].as_long()

    itinerary = [
        {"action": "meet", "person": "Karen", "start_time": to_time(sk_val), "end_time": to_time(sk_val + 30)},
        {"action": "meet", "person": "Anthony", "start_time": to_time(sa_val), "end_time": to_time(sa_val + 105)},
        {"action": "meet", "person": "Betty", "start_time": to_time(sb_val), "end_time": to_time(sb_val + 15)},
    ]
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))
else:
    # Second sequence: Anthony -> Karen -> Betty
    s_a_seq2 = Int('s_a_seq2')
    s_k_seq2 = Int('s_k_seq2')
    s_b_seq2 = Int('s_b_seq2')
    e_a_seq2 = s_a_seq2 + 105
    e_k_seq2 = s_k_seq2 + 30
    e_b_seq2 = s_b_seq2 + 15

    constraints_seq2 = [
        # Anthony's meeting
        s_a_seq2 >= 559,  # arrival at FD from Bayview (19 min)
        s_a_seq2 >= 555,  # Anthony's earliest start
        s_a_seq2 <= 1185,  # Anthony's latest start

        # Karen's meeting
        s_k_seq2 >= e_a_seq2 + 10,  # travel time from FD to Fisherman's is 10 min
        e_k_seq2 <= 900,  # ends by 3 PM

        # Betty's meeting
        s_b_seq2 >= e_k_seq2 + 8,  # travel time from Fisherman's to Embarcadero is 8 min
        s_b_seq2 >= 1185,  # Betty's earliest start
        s_b_seq2 <= 1275,  # Betty's latest start
    ]

    solver_seq2 = Solver()
    solver_seq2.add(constraints_seq2)

    if solver_seq2.check() == sat:
        model_seq2 = solver_seq2.model()
        sa_val_seq2 = model_seq2[s_a_seq2].as_long()
        sk_val_seq2 = model_seq2[s_k_seq2].as_long()
        sb_val_seq2 = model_seq2[s_b_seq2].as_long()

        itinerary_seq2 = [
            {"action": "meet", "person": "Anthony", "start_time": to_time(sa_val_seq2), "end_time": to_time(sa_val_seq2 + 105)},
            {"action": "meet", "person": "Karen", "start_time": to_time(sk_val_seq2), "end_time": to_time(sk_val_seq2 + 30)},
            {"action": "meet", "person": "Betty", "start_time": to_time(sb_val_seq2), "end_time": to_time(sb_val_seq2 + 15)},
        ]
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary_seq2}))
    else:
        print("No solution found.")