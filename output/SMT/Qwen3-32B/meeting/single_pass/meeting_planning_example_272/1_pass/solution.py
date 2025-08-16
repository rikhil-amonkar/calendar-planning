import z3

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = z3.Solver()

T_start = z3.Int('T_start')
P_start = z3.Int('P_start')
A_start = z3.Int('A_start')

# Timothy's constraints
solver.add(T_start >= 9 * 60 + 45)  # 9:45 AM
solver.add(T_start <= 17 * 60 + 45 - 120)  # 17:45 PM - 120 min

# Patricia's constraints
solver.add(P_start >= T_start + 120 + 10)  # Travel time from Embarcadero to Nob Hill
solver.add(P_start >= 18 * 60 + 30)  # 18:30 PM
solver.add(P_start <= 21 * 60 + 45 - 90)  # 21:45 PM - 90 min

# Ashley's constraints
solver.add(A_start >= P_start + 90 + 13)  # Travel time from Nob Hill to Mission
solver.add(A_start >= 20 * 60 + 30)  # 20:30 PM
solver.add(A_start <= 21 * 60 + 15 - 45)  # 21:15 PM - 45 min

if solver.check() == z3.sat:
    model = solver.model()
    t_start_val = model[T_start].as_long()
    p_start_val = model[P_start].as_long()
    a_start_val = model[A_start].as_long()

    t_end = t_start_val + 120
    p_end = p_start_val + 90
    a_end = a_start_val + 45

    itinerary = [
        {"action": "meet", "person": "Timothy", "start_time": minutes_to_time(t_start_val), "end_time": minutes_to_time(t_end)},
        {"action": "meet", "person": "Patricia", "start_time": minutes_to_time(p_start_val), "end_time": minutes_to_time(p_end)},
        {"action": "meet", "person": "Ashley", "start_time": minutes_to_time(a_start_val), "end_time": minutes_to_time(a_end)}
    ]

    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")