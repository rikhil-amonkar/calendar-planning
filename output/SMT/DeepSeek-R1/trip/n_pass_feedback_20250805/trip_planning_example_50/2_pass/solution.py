from z3 import *
import json

# Define the variables for start and end days of each segment
v_start, v_end = Int('v_start'), Int('v_end')
m_start, m_end = Int('m_start'), Int('m_end')
k_start, k_end = Int('k_start'), Int('k_end')

solver = Solver()

# Constraints for the segments
solver.add(v_start == 1)            # Start day of Vilnius is day 1
solver.add(v_end == m_start)         # End day of Vilnius is start day of Munich
solver.add(m_end == k_start)         # End day of Munich is start day of Mykonos
solver.add(k_end == 12)              # End day of Mykonos is day 12

# Duration constraints for each city
solver.add(v_end - v_start + 1 == 4)   # Vilnius: 4 days
solver.add(m_end - m_start + 1 == 3)   # Munich: 3 days
solver.add(k_end - k_start + 1 == 7)   # Mykonos: 7 days

# Ensure days are within valid range and in order
solver.add(v_end >= v_start)
solver.add(m_end >= m_start)
solver.add(k_end >= k_start)
solver.add(m_start >= v_end)
solver.add(k_start >= m_end)

if solver.check() == sat:
    m = solver.model()
    vs = m[v_start].as_long()
    ve = m[v_end].as_long()
    ms = m[m_start].as_long()
    me = m[m_end].as_long()
    ks = m[k_start].as_long()
    ke = m[k_end].as_long()
    
    itinerary = []
    for day in range(1, 13):
        places = []
        if vs <= day <= ve:
            places.append("Vilnius")
        if ms <= day <= me:
            places.append("Munich")
        if ks <= day <= ke:
            places.append("Mykonos")
        itinerary.append({"day": day, "place": places})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')