from z3 import Int, Solver, sat
import json

# Initialize Z3 solver and variables
s = Solver()
vs, ve = Int('vs'), Int('ve')  # Vilnius start and end
ms, me = Int('ms'), Int('me')  # Munich start and end
ks, ke = Int('ks'), Int('ke')  # Mykonos start and end

# Fixed start and end constraints
s.add(vs == 1)  # Trip starts in Vilnius on day 1
s.add(ke == 12)  # Trip ends in Mykonos on day 12

# Transition constraints (flight days)
s.add(ve == ms)  # Vilnius end = Munich start (flight day)
s.add(me == ks)  # Munich end = Mykonos start (flight day)

# Duration constraints (inclusive of transition days)
s.add(ve - vs + 1 == 4)  # Vilnius: 4 days
s.add(me - ms + 1 == 3)  # Munich: 3 days
s.add(ke - ks + 1 == 7)  # Mykonos: 7 days

# Validate segment ordering
s.add(ve >= vs, me >= ms, ke >= ks)  # Valid day ranges
s.add(ms >= vs, me >= ms, ks >= me, ke >= ks)  # Monotonic progression

if s.check() == sat:
    m = s.model()
    # Extract segment boundaries
    vs_val = m[vs].as_long()
    ve_val = m[ve].as_long()
    ms_val = m[ms].as_long()
    me_val = m[me].as_long()
    ks_val = m[ks].as_long()
    ke_val = m[ke].as_long()
    
    # Construct itinerary with overlapping transition days
    itinerary = [
        {"day_range": f"Day {vs_val}-{ve_val}", "place": "Vilnius"},
        {"day_range": f"Day {ms_val}-{me_val}", "place": "Munich"},
        {"day_range": f"Day {ks_val}-{ke_val}", "place": "Mykonos"}
    ]
    print(json.dumps({"itinerary": itinerary}))
else:
    print('{"itinerary": []}')  # No solution found