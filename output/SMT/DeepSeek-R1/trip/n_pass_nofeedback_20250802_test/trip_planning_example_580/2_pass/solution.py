from z3 import *

# Define the variables for the start days of the blocks (except the first which is fixed at 1)
s1 = Int('s1')  # start of the second block (Paris in our fixed order)
s2 = Int('s2')  # start of the third block (Porto)
s3 = Int('s3')  # start of the fourth block (Reykjavik)
s4 = Int('s4')  # start of the fifth block (Oslo)

s = Solver()

# Constraints for the start days
s.add(s1 >= 4, s1 <= 12)
s.add(s2 >= s1 + 3, s2 <= 15)
s.add(s3 >= s2 + 3, s3 <= 18)
s.add(s4 >= s3 + 3, s4 <= 21)

if s.check() == sat:
    m = s.model()
    s1_val = m.eval(s1).as_long()
    s2_val = m.eval(s2).as_long()
    s3_val = m.eval(s3).as_long()
    s4_val = m.eval(s4).as_long()
    
    # Calculate end days for each block
    # Block0: Geneva from day 1 to s1_val-1
    # Block1: Paris from day s1_val to s2_val-1
    # Block2: Porto from day s2_val to s3_val-1
    # Block3: Reykjavik from day s3_val to s4_val-1
    # Block4: Oslo from day s4_val to 23
    itinerary = [
        {'day_range': f"Day 1-{s1_val-1}", 'place': 'Geneva'},
        {'day_range': f"Day {s1_val}-{s2_val-1}", 'place': 'Paris'},
        {'day_range': f"Day {s2_val}-{s3_val-1}", 'place': 'Porto'},
        {'day_range': f"Day {s3_val}-{s4_val-1}", 'place': 'Reykjavik'},
        {'day_range': f"Day {s4_val}-23", 'place': 'Oslo'}
    ]
    plan = {'itinerary': itinerary}
    print("Plan found:", plan)
else:
    print("No plan found")