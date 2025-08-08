from z3 import *

def format_time(minutes):
    hours = minutes // 60
    minutes_remainder = minutes % 60
    return f"{hours:02d}:{minutes_remainder:02d}"

s = Solver()

# Define variables
Laura_first = Bool('Laura_first')
t0 = Int('t0')   # time leaving Castro (minutes from 9:00)

L_start = Int('L_start')
L_end = Int('L_end')
A_start = Int('A_start')
A_end = Int('A_end')

# Constraints for both orders
c1 = And(
    L_start >= t0 + 7,
    L_start >= 195,  # 12:15 PM is 195 minutes from 9:00
    L_end == L_start + 75,
    L_end <= 645,   # 7:45 PM is 645 minutes from 9:00
    A_start >= L_end + 17,  # travel from Mission to Financial
    A_start >= 210,  # 12:30 PM is 210 minutes from 9:00
    A_end == A_start + 30,
    A_end <= 345    # 2:45 PM is 345 minutes from 9:00
)

c2 = And(
    A_start >= t0 + 20,  # travel from Castro to Financial
    A_start >= 210,
    A_end == A_start + 30,
    A_end <= 345,
    L_start >= A_end + 17,  # travel from Financial to Mission
    L_start >= 195,
    L_end == L_start + 75,
    L_end <= 645
)

s.add(Or(And(Laura_first, c1), And(Not(Laura_first), c2)))
s.add(t0 >= 0)

if s.check() == sat:
    m = s.model()
    t0_val = m.eval(t0).as_long()
    L_start_val = m.eval(L_start).as_long()
    L_end_val = m.eval(L_end).as_long()
    A_start_val = m.eval(A_start).as_long()
    A_end_val = m.eval(A_end).as_long()
    laura_first_val = is_true(m.eval(Laura_first))
    
    base_minutes = 9 * 60  # 9:00 AM in minutes from 00:00
    
    abs_L_start = base_minutes + L_start_val
    abs_L_end = base_minutes + L_end_val
    abs_A_start = base_minutes + A_start_val
    abs_A_end = base_minutes + A_end_val
    
    if laura_first_val:
        itinerary = [
            {"action": "meet", "person": "Laura", "start_time": format_time(abs_L_start), "end_time": format_time(abs_L_end)},
            {"action": "meet", "person": "Anthony", "start_time": format_time(abs_A_start), "end_time": format_time(abs_A_end)}
        ]
    else:
        itinerary = [
            {"action": "meet", "person": "Anthony", "start_time": format_time(abs_A_start), "end_time": format_time(abs_A_end)},
            {"action": "meet", "person": "Laura", "start_time": format_time(abs_L_start), "end_time": format_time(abs_L_end)}
        ]
    
    result = {"itinerary": itinerary}
    print(f"SOLUTION: {result}")
else:
    print("No solution found")