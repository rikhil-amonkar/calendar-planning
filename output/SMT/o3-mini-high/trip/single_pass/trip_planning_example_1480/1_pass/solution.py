from z3 import *

# City indices and names
cities = ["Geneva", "Istanbul", "Madrid", "Venice", "Munich", 
          "Vienna", "Riga", "Vilnius", "Reykjavik", "Brussels"]
# durations for each city (in days)
durations = [4, 4, 4, 5, 5, 4, 2, 4, 2, 2]

# Create a solver instance
solver = Solver()

n = len(cities)

# order[i] will be the index of the city in the i-th position.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    solver.add(And(order[i] >= 0, order[i] < n))
solver.add(Distinct(order))

# Force Brussels (index 9) to be last (position 9)
solver.add(order[n-1] == 9)

# S[i] is the start day when we begin our stay in the city at position i.
S = [Int(f"S_{i}") for i in range(n)]
solver.add(S[0] == 1)
# For each position i, the finish day of that block is: F[i] = S[i] + durations[city at position i] - 1.
# And because the flight day is shared between consecutive segments we enforce:
#    S[i+1] = S[i] + (duration(city at pos i)-1)
for i in range(1, n):
    # Use piecewise sums: add (durations[k]-1) if city k is chosen at position i-1.
    solver.add(S[i] == S[i-1] + 
               Sum([If(order[i-1] == k, durations[k] - 1, 0) for k in range(n)]))

# The overall trip should end on day 27.
# Since F[n-1] = S[n-1] + (duration(city at last) - 1) and last city is Brussels (duration 2):
# we have: S[9] + 1 = 27, so S[9] must be 26.
solver.add(S[n-1] == 26)

# Add event–time constraints.
# If the city appears in a given slot then S[i] must lie in the following range:
# Geneva (index 0): relatives between day 1 and 4  => S <= 4
# Venice (index 3): workshop between day 7 and 11 => need S in [3, 11] (since block = [S, S+4] then day7 falls if S>=3)
# Vilnius (index 7): friends meet between day 20 and 23 => need S in [17, 23]
# Brussels (index 9): wedding between day 26 and 27 => need S in [25, 27] (we already force S to 26 in the last slot)
for i in range(n):
    # For Geneva:
    solver.add(Implies(order[i] == 0, S[i] <= 4))
    # For Venice:
    solver.add(Implies(order[i] == 3, And(S[i] >= 3, S[i] <= 11)))
    # For Vilnius:
    solver.add(Implies(order[i] == 7, And(S[i] >= 17, S[i] <= 23)))
    # For Brussels:
    solver.add(Implies(order[i] == 9, And(S[i] >= 25, S[i] <= 27)))

# Now, add the flight connectivity constraints.
# For every consecutive pair positions (i, i+1) the chosen cities must be connected
# by a direct flight (using only the allowed list).
valid_flights = [
    (4,5), (5,4),           # Munich <-> Vienna
    (1,9), (9,1),           # Istanbul <-> Brussels
    (5,7), (7,5),           # Vienna <-> Vilnius
    (2,4), (4,2),           # Madrid <-> Munich
    (3,9), (9,3),           # Venice <-> Brussels
    (6,9), (9,6),           # Riga <-> Brussels
    (0,1), (1,0),           # Geneva <-> Istanbul
    (4,8), (8,4),           # Munich <-> Reykjavik
    (5,1), (1,5),           # Vienna <-> Istanbul
    (6,1), (1,6),           # Riga <-> Istanbul
    (8,5), (5,8),           # Reykjavik <-> Vienna
    (3,4), (4,3),           # Venice <-> Munich
    (2,3), (3,2),           # Madrid <-> Venice
    (7,1), (1,7),           # Vilnius <-> Istanbul
    (3,5), (5,3),           # Venice <-> Vienna
    (3,1), (1,3),           # Venice <-> Istanbul
    (8,2),                 # from Reykjavik to Madrid (directed only)
    (6,4),                 # from Riga to Munich (directed only)
    (4,1), (1,4),           # Munich <-> Istanbul
    (8,9), (9,8),           # Reykjavik <-> Brussels
    (7,9), (9,7),           # Vilnius <-> Brussels
    (7,4),                 # from Vilnius to Munich (directed only)
    (2,5), (5,2),           # Madrid <-> Vienna
    (5,6), (6,5),           # Vienna <-> Riga
    (0,5), (5,0),           # Geneva <-> Vienna
    (2,9), (9,2),           # Madrid <-> Brussels
    (0,2), (2,0),           # Geneva <-> Madrid
    (0,4), (4,0),           # Geneva <-> Munich
    (6,7)                  # from Riga to Vilnius (directed only)
]

# For every adjacent pair in the order, force that the (a,b) pair is one of the allowed ones.
for i in range(n - 1):
    # Build the disjunction of allowed pairs for this adjacent pair.
    allowed = []
    for (a, b) in valid_flights:
        allowed.append(And(order[i] == a, order[i+1] == b))
    solver.add(Or(allowed))

# Solve the model.
if solver.check() == sat:
    mod = solver.model()
    # Reconstruct the order and start times in order of positions 0..9.
    sol_order = [mod.evaluate(order[i]).as_long() for i in range(n)]
    sol_S = [mod.evaluate(S[i]).as_long() for i in range(n)]
    itinerary = []
    for i in range(n):
        city = cities[sol_order[i]]
        start = sol_S[i]
        end = start + durations[sol_order[i]] - 1
        itinerary.append({
          "city": city,
          "start_day": start,
          "end_day": end
        })
    import json
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")