#!/usr/bin/env python3
import json
from z3 import Solver, Int, And, Or, If, Distinct, Implies, sat

# Define city names and their required durations (in days)
cities = {
    0: "Istanbul",
    1: "Vienna",
    2: "Riga",
    3: "Brussels",
    4: "Madrid",
    5: "Vilnius",
    6: "Venice",
    7: "Geneva",
    8: "Munich",
    9: "Reykjavik"
}

durations = {
    0: 4,  # Istanbul
    1: 4,  # Vienna
    2: 2,  # Riga
    3: 2,  # Brussels
    4: 4,  # Madrid
    5: 4,  # Vilnius
    6: 5,  # Venice
    7: 4,  # Geneva
    8: 5,  # Munich
    9: 2   # Reykjavik
}

# Allowed direct flights.
# For flights specified as "A and B", we add both directions.
# For flights specified as "from X to Y", we add only that directed edge.
allowed_edges = set()

def add_bidirectional(a, b):
    allowed_edges.add((a, b))
    allowed_edges.add((b, a))

def add_directed(a, b):
    allowed_edges.add((a, b))

# 1. Munich and Vienna
add_bidirectional(8, 1)
# 2. Istanbul and Brussels
add_bidirectional(0, 3)
# 3. Vienna and Vilnius
add_bidirectional(1, 5)
# 4. Madrid and Munich
add_bidirectional(4, 8)
# 5. Venice and Brussels
add_bidirectional(6, 3)
# 6. Riga and Brussels
add_bidirectional(2, 3)
# 7. Geneva and Istanbul
add_bidirectional(7, 0)
# 8. Munich and Reykjavik
add_bidirectional(8, 9)
# 9. Vienna and Istanbul
add_bidirectional(1, 0)
# 10. Riga and Istanbul
add_bidirectional(2, 0)
# 11. Reykjavik and Vienna
add_bidirectional(9, 1)
# 12. Venice and Munich
add_bidirectional(6, 8)
# 13. Madrid and Venice
add_bidirectional(4, 6)
# 14. Vilnius and Istanbul
add_bidirectional(5, 0)
# 15. Venice and Vienna
add_bidirectional(6, 1)
# 16. Venice and Istanbul
add_bidirectional(6, 0)
# 17. from Reykjavik to Madrid
add_directed(9, 4)
# 18. from Riga to Munich
add_directed(2, 8)
# 19. Munich and Istanbul
add_bidirectional(8, 0)
# 20. Reykjavik and Brussels
add_bidirectional(9, 3)
# 21. Vilnius and Brussels
add_bidirectional(5, 3)
# 22. from Vilnius to Munich
add_directed(5, 8)
# 23. Madrid and Vienna
add_bidirectional(4, 1)
# 24. Vienna and Riga
add_bidirectional(1, 2)
# 25. Geneva and Vienna
add_bidirectional(7, 1)
# 26. Madrid and Brussels
add_bidirectional(4, 3)
# 27. Vienna and Brussels
add_bidirectional(1, 3)
# 28. Geneva and Brussels
add_bidirectional(7, 3)
# 29. Geneva and Madrid
add_bidirectional(7, 4)
# 30. Munich and Brussels
add_bidirectional(8, 3)
# 31. Madrid and Istanbul
add_bidirectional(4, 0)
# 32. Geneva and Munich
add_bidirectional(7, 8)
# 33. from Riga to Vilnius
add_directed(2, 5)

# Create SMT solver
solver = Solver()

n = 10  # number of cities to visit

# Create itinerary variables: itinerary[i] is the city index visited in the i-th slot.
itinerary = [Int(f"city_{i}") for i in range(n)]
# Create time variables: s[i] = start day in city at position i, e[i] = end day in that city.
s_vars = [Int(f"s_{i}") for i in range(n)]
e_vars = [Int(f"e_{i}") for i in range(n)]

# Domain constraints for itinerary cities (0..9) and distinctness.
for i in range(n):
    solver.add(itinerary[i] >= 0, itinerary[i] <= 9)
solver.add(Distinct(itinerary))

# Helper: given a city variable, return its duration using nested If.
def duration_expr(city_var):
    return If(city_var == 0, durations[0],
        If(city_var == 1, durations[1],
            If(city_var == 2, durations[2],
                If(city_var == 3, durations[3],
                    If(city_var == 4, durations[4],
                        If(city_var == 5, durations[5],
                            If(city_var == 6, durations[6],
                                If(city_var == 7, durations[7],
                                    If(city_var == 8, durations[8],
                                        If(city_var == 9, durations[9], 0)
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )
    )

# Chain constraints:
# The trip starts on day 1.
solver.add(s_vars[0] == 1)
# For each city in the itinerary, set its end time from its start time and duration.
for i in range(n):
    dur = duration_expr(itinerary[i])
    solver.add(e_vars[i] == s_vars[i] + dur - 1)
    if i > 0:
        # if flying from previous city, the flight day counts for both => start day = previous end day.
        solver.add(s_vars[i] == e_vars[i-1])
# The overall trip must last 27 days (i.e. the last day is day 27).
solver.add(e_vars[n-1] == 27)

# Flight connectivity constraints for consecutive cities.
for i in range(n - 1):
    allowed_flight_conditions = []
    for (a, b) in allowed_edges:
        allowed_flight_conditions.append(And(itinerary[i] == a, itinerary[i+1] == b))
    solver.add(Or(allowed_flight_conditions))

# Event constraints:
# - Attend a wedding in Brussels (city 3) between day 26 and day 27.
for i in range(n):
    solver.add(Implies(itinerary[i] == 3, And(s_vars[i] <= 27, e_vars[i] >= 26)))
# - Attend a workshop in Venice (city 6) between day 7 and day 11.
for i in range(n):
    solver.add(Implies(itinerary[i] == 6, And(s_vars[i] <= 11, e_vars[i] >= 7)))
# - Meet friends in Vilnius (city 5) between day 20 and day 23.
for i in range(n):
    solver.add(Implies(itinerary[i] == 5, And(s_vars[i] <= 23, e_vars[i] >= 20)))
# - Visit relatives in Geneva (city 7) between day 1 and day 4.
for i in range(n):
    solver.add(Implies(itinerary[i] == 7, And(s_vars[i] <= 4, e_vars[i] >= 1)))

# Check and extract a solution.
if solver.check() == sat:
    model = solver.model()
    itinerary_list = []
    for i in range(n):
        city_idx = model[itinerary[i]].as_long()
        start_day = model[s_vars[i]].as_long()
        end_day = model[e_vars[i]].as_long()
        itinerary_list.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": cities[city_idx]
        })
    result = {"itinerary": itinerary_list}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))