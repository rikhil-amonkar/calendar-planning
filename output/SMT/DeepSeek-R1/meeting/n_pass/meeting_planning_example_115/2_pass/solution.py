from z3 import *

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Initialize optimizer
opt = Optimize()

# Define variables in minutes (integers)
C_start = Int('C_start')
J_start = Int('J_start')

# Convert times to minutes
start_of_day = 9 * 60  # 9:00 in minutes

# Carol available: 11:30 (690) to 15:00 (900), meeting duration 60 minutes
carol_available_start = 11 * 60 + 30   # 690
carol_available_end = 15 * 60          # 900
# Carol must start by 14:00 (840) to end by 15:00
opt.add(C_start >= carol_available_start)
opt.add(C_start <= carol_available_end - 60)  # C_start <= 840

# Jessica available: 15:30 (930) to 16:45 (1005), meeting duration 45 minutes
jessica_available_start = 15 * 60 + 30  # 930
jessica_available_end = 16 * 60 + 45    # 1005
opt.add(J_start >= jessica_available_start)
opt.add(J_start <= jessica_available_end - 45)  # J_start <= 960

# Travel constraints
# From Richmond to Marina: 9 minutes -> leave Richmond at C_start - 9
opt.add(C_start - 9 >= start_of_day)
# From Marina to Pacific Heights: 7 minutes, leave Marina at C_start + 60, arrive at C_start + 67
opt.add(C_start + 67 <= J_start)

# Optimize: minimize Jessica's start time to reduce total waiting, then maximize Carol's start time
opt.minimize(J_start)
opt.maximize(C_start)

if opt.check() == sat:
    m = opt.model()
    c_start_val = m.eval(C_start).as_long()
    j_start_val = m.eval(J_start).as_long()
    
    carol_end = c_start_val + 60
    jessica_end = j_start_val + 45
    
    itinerary = [
        {"action": "meet", "person": "Carol", "start_time": min_to_time(c_start_val), "end_time": min_to_time(carol_end)},
        {"action": "meet", "person": "Jessica", "start_time": min_to_time(j_start_val), "end_time": min_to_time(jessica_end)}
    ]
    
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(result)
else:
    print("No solution found")