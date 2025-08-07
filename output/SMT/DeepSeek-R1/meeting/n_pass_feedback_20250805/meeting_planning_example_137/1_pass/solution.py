from z3 import *

def min_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Define variables
b_start = Int('b_start')
b_end = Int('b_end')
k_start = Int('k_start')
k_end = Int('k_end')
order = Bool('order')  # True: Barbara first, False: Kenneth first

s = Optimize()

# Constraints for Barbara
s.add(b_start >= 0, b_start <= 1140)
s.add(b_end >= 0, b_end <= 1140)
s.add(b_end - b_start >= 45)

# Constraints for Kenneth
s.add(k_start >= 0, k_start <= 900)
s.add(k_end >= 0, k_end <= 900)
s.add(k_end - k_start >= 90)
s.add(k_start >= 720, k_end <= 900)

# Constraints based on order
s.add(If(order, 
         And(
             b_start >= 563,  # Arrival at Golden Gate Park at 9:23 AM (540 + 23 = 563 minutes)
             k_start >= b_end + 23,  # Travel from Golden Gate Park to Chinatown takes 23 minutes
             k_start >= 720  # Kenneth available from 12:00 PM
         ),
         And(
             k_start >= 545,  # Arrival at Chinatown at 9:05 AM (540 + 5 = 545 minutes), but must wait until 12:00 PM
             b_start >= k_end + 23,  # Travel from Chinatown to Golden Gate Park takes 23 minutes
             b_end <= 1140
         )))

# Minimize the end time of the last meeting
last_end = If(order, k_end, b_end)
s.minimize(last_end)

# Check for a solution
if s.check() == sat:
    m = s.model()
    b_start_val = m[b_start].as_long()
    b_end_val = m[b_end].as_long()
    k_start_val = m[k_start].as_long()
    k_end_val = m[k_end].as_long()
    order_val = m[order]
    
    itinerary = []
    if is_true(order_val):
        itinerary.append({
            "action": "meet",
            "person": "Barbara",
            "start_time": min_to_time(b_start_val),
            "end_time": min_to_time(b_end_val)
        })
        itinerary.append({
            "action": "meet",
            "person": "Kenneth",
            "start_time": min_to_time(k_start_val),
            "end_time": min_to_time(k_end_val)
        })
    else:
        itinerary.append({
            "action": "meet",
            "person": "Kenneth",
            "start_time": min_to_time(k_start_val),
            "end_time": min_to_time(k_end_val)
        })
        itinerary.append({
            "action": "meet",
            "person": "Barbara",
            "start_time": min_to_time(b_start_val),
            "end_time": min_to_time(b_end_val)
        })
    
    print('SOLUTION:')
    print(f'{{"itinerary": {itinerary}}}')
else:
    print("No solution found")