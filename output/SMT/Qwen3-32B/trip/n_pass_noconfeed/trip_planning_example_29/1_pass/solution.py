from z3 import *
import json

solver = Solver()

# Define city order variables (0: Dubrovnik, 1: Frankfurt, 2: Krakow)
c1, c2, c3 = Ints('c1 c2 c3')
solver.add(And(0 <= c1, c1 <= 2))
solver.add(And(0 <= c2, c2 <= 2))
solver.add(And(0 <= c3, c3 <= 2))
solver.add(Distinct(c1, c2, c3))

# Allowed transitions between cities
allowed_transitions_1 = Or(
    And(c1 == 0, c2 == 1),  # Dubrovnik -> Frankfurt
    And(c1 == 1, c2 == 0),  # Frankfurt -> Dubrovnik
    And(c1 == 1, c2 == 2),  # Frankfurt -> Krakow
    And(c1 == 2, c2 == 1)   # Krakow -> Frankfurt
)
allowed_transitions_2 = Or(
    And(c2 == 0, c3 == 1),  # Dubrovnik -> Frankfurt
    And(c2 == 1, c3 == 0),  # Frankfurt -> Dubrovnik
    And(c2 == 1, c3 == 2),  # Frankfurt -> Krakow
    And(c2 == 2, c3 == 1)   # Krakow -> Frankfurt
)
solver.add(allowed_transitions_1)
solver.add(allowed_transitions_2)

# Transition days
t1, t2 = Ints('t1 t2')

# Required durations for each city
required_duration_c1 = If(c1 == 0, 7, If(c1 == 1, 3, 2))
required_duration_c2 = If(c2 == 0, 7, If(c2 == 1, 3, 2))
required_duration_c3 = If(c3 == 0, 7, If(c3 == 1, 3, 2))

# Duration constraints
solver.add(t1 == required_duration_c1)
solver.add(t2 - t1 + 1 == required_duration_c2)
solver.add(10 - t2 + 1 == required_duration_c3)

# Additional constraints for transition days
solver.add(t1 >= 1)
solver.add(t2 >= t1)
solver.add(t2 <= 10)

if solver.check() == sat:
    model = solver.model()
    city_order = [model[c1].as_long(), model[c2].as_long(), model[c3].as_long()]
    t1_val = model[t1].as_long()
    t2_val = model[t2].as_long()
    
    city_names = {0: "Dubrovnik", 1: "Frankfurt", 2: "Krakow"}
    
    itinerary = []
    # First city
    itinerary.append({"day_range": f"Day 1-{t1_val}", "place": city_names[city_order[0]]})
    # Second city
    itinerary.append({"day_range": f"Day {t1_val}-{t2_val}", "place": city_names[city_order[1]]})
    # Third city
    itinerary.append({"day_range": f"Day {t2_val}-10", "place": city_names[city_order[2]]})
    
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))