from z3 import *

# Convert time to minutes since midnight
def to_minutes(h, m):
    return h * 60 + m

# Convert minutes back to time string
def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

s = Solver()

# Variables
E_start = Int('E_start')  # Start time of Emily's meeting in minutes
A_E = Int('A_E')          # Arrival time at Union Square
D_RH = Int('D_RH')        # Departure time from Russian Hill to Union Square

# Constants
start_NB = to_minutes(9, 0)   # 9:00 AM at North Beach
emily_earliest = to_minutes(16, 0)  # 4:00 PM
emily_latest_start = to_minutes(16, 30)  # 4:30 PM (since meeting needs 45 min)
travel_NB_to_US = 7
travel_RH_to_US = 11
travel_US_to_RH = 13
arrival_RH_after_emily = Int('arrival_RH_after_emily')

# Emily's meeting constraints
s.add(E_start >= emily_earliest)
s.add(E_start <= emily_latest_start)
s.add(E_start + 45 <= to_minutes(17, 15))  # Ends by 5:15 PM

# Arrival at Union Square must be <= E_start and >= possible arrival times
s.add(A_E <= E_start)

# Route possibilities: direct from NB or via Russian Hill
route_direct = And(A_E == start_NB + travel_NB_to_US + D1, D1 >= 0)
route_via_rh = And(
    D_RH >= start_NB + 4,  # Arrival at Russian Hill at 9:04
    A_E == D_RH + travel_RH_to_US
)

D1 = Int('D1')  # Time spent at NB before leaving for US in direct route
s.add(Or(route_direct, route_via_rh))

# Arrival at Russian Hill after meeting Emily must be before 7 PM
s.add(arrival_RH_after_emily == E_start + 45 + travel_US_to_RH)
s.add(arrival_RH_after_emily <= to_minutes(19, 0))  # Must arrive by 7 PM

if s.check() == sat:
    m = s.model()
    e_start = m[E_start].as_long()
    a_e = m[A_E].as_long()
    arrival_rh = m[arrival_RH_after_emily].as_long()
    
    print("Optimal Schedule:")
    print(f"9:00 AM - Depart North Beach")
    if m.evaluate(route_direct):
        dep_NB = start_NB + m[D1].as_long()
        print(f"{to_time_str(dep_NB)} - Travel to Union Square (7 min)")
    else:
        dep_rh = m[D_RH].as_long()
        print(f"{to_time_str(start_NB + 4)} - Arrive Russian Hill")
        print(f"{to_time_str(dep_rh)} - Depart Russian Hill to Union Square (11 min)")
    print(f"{to_time_str(a_e)} - Arrive Union Square")
    print(f"{to_time_str(e_start)} - Meet Emily (45 min until {to_time_str(e_start + 45)})")
    print(f"{to_time_str(e_start + 45)} - Travel to Russian Hill (13 min)")
    print(f"{to_time_str(arrival_rh)} - Arrive Russian Hill")
    print(f"19:00 - Meet Margaret (120 min until 21:00)")
else:
    print("No valid schedule found.")