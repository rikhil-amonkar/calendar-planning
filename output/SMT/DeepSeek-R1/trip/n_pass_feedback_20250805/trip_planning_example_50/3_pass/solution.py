from z3 import Int, Solver, sat
import json

# Initialize Z3 variables for start and end days of each city segment
v_start, v_end = Int('v_start'), Int('v_end')
m_start, m_end = Int('m_start'), Int('m_end')
k_start, k_end = Int('k_start'), Int('k_end')

solver = Solver()

# Fixed start and end constraints
solver.add(v_start == 1)        # Trip starts in Vilnius on day 1
solver.add(k_end == 12)         # Trip ends in Mykonos on day 12

# Segment transition constraints
solver.add(v_end == m_start)    # Flight from Vilnius to Munich on transition day
solver.add(m_end == k_start)    # Flight from Munich to Mykonos on transition day

# Duration constraints (inclusive of transition days)
solver.add(v_end - v_start + 1 == 4)  # Vilnius: 4 days
solver.add(m_end - m_start + 1 == 3)  # Munich: 3 days
solver.add(k_end - k_start + 1 == 7)  # Mykonos: 7 days

# Validate day ordering
solver.add(v_start <= v_end, m_start <= m_end, k_start <= k_end)
solver.add(v_end >= v_start, m_end >= m_start, k_end >= k_start)
solver.add(m_start >= v_end, k_start >= m_end)  # Ensure no gaps between segments

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    # Extract values from the model
    vs = model[v_start].as_long()
    ve = model[v_end].as_long()
    ms = model[m_start].as_long()
    me = model[m_end].as_long()
    ks = model[k_start].as_long()
    ke = model[k_end].as_long()
    
    # Build the itinerary
    itinerary = []
    for day in range(1, 13):  # Days 1 to 12
        cities = []
        if vs <= day <= ve:
            cities.append("Vilnius")
        if ms <= day <= me:
            cities.append("Munich")
        if ks <= day <= ke:
            cities.append("Mykonos")
        itinerary.append({"day": day, "place": cities})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print('{"itinerary": []}')  # Fallback if no solution found