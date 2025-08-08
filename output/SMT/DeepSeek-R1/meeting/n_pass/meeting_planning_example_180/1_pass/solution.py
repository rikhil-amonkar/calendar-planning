from z3 import *
import json

# Travel times in minutes
T_NB_MD = 18  # North Beach to Mission District
T_NB_TC = 22  # North Beach to The Castro
T_MD_TC = 7   # Mission District to The Castro
T_TC_MD = 7   # The Castro to Mission District

# Convert time to minutes from 9:00 AM
james_avail_start = 225  # 12:45 PM
james_avail_end = 300    # 2:00 PM
robert_avail_start = 225 # 12:45 PM
robert_avail_end = 375   # 3:15 PM

# Create variables
S1 = Int('S1')  # start time of first meeting
E1 = Int('E1')  # end time of first meeting
S2 = Int('S2')  # start time of second meeting
E2 = Int('E2')  # end time of second meeting
order = Int('order')  # 0: first James then Robert, 1: first Robert then James

s = Solver()

# order must be either 0 or 1
s.add(Or(order == 0, order == 1))

# Common constraints: times are nonnegative and meetings have positive duration
s.add(S1 >= 0, E1 >= 0, S2 >= 0, E2 >= 0)
s.add(E1 >= S1, E2 >= S2)

# Constraints based on order
s.add(If(order == 0,
    And(
        S1 >= T_NB_MD,  # travel time to first meeting (MD) from NB
        S1 >= james_avail_start,
        E1 <= james_avail_end,
        E1 - S1 >= 75,   # meet James for at least 75 minutes
        S2 >= E1 + T_MD_TC,  # travel from MD to TC after first meeting
        S2 >= robert_avail_start,
        E2 <= robert_avail_end,
        E2 - S2 >= 30    # meet Robert for at least 30 minutes
    ),
    And(
        S1 >= T_NB_TC,  # travel time to first meeting (TC) from NB
        S1 >= robert_avail_start,
        E1 <= robert_avail_end,
        E1 - S1 >= 30,   # meet Robert for at least 30 minutes
        S2 >= E1 + T_TC_MD,  # travel from TC to MD after first meeting
        S2 >= james_avail_start,
        E2 <= james_avail_end,
        E2 - S2 >= 75    # meet James for at least 75 minutes
    )
))

# Check for a solution
if s.check() == sat:
    m = s.model()
    order_val = m[order].as_long()
    S1_val = m[S1].as_long()
    E1_val = m[E1].as_long()
    S2_val = m[S2].as_long()
    E2_val = m[E2].as_long()
    
    # Convert minutes to time string (24-hour format)
    def min_to_time(t):
        total_minutes = t
        hours = total_minutes // 60
        minutes = total_minutes % 60
        hour = 9 + hours
        return f"{hour:02d}:{minutes:02d}"
    
    if order_val == 0:
        meeting1 = {"action": "meet", "person": "James", "start_time": min_to_time(S1_val), "end_time": min_to_time(E1_val)}
        meeting2 = {"action": "meet", "person": "Robert", "start_time": min_to_time(S2_val), "end_time": min_to_time(E2_val)}
    else:
        meeting1 = {"action": "meet", "person": "Robert", "start_time": min_to_time(S1_val), "end_time": min_to_time(E1_val)}
        meeting2 = {"action": "meet", "person": "James", "start_time": min_to_time(S2_val), "end_time": min_to_time(E2_val)}
    
    itinerary = [meeting1, meeting2]
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result))
else:
    print("SOLUTION:")
    print(json.dumps({"itinerary": []}))