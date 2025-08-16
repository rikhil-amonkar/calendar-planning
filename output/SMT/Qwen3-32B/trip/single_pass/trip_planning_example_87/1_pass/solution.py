import json
from z3 import *

def main():
    solver = Solver()

    a1 = Int('a1')
    d1 = Int('d1')
    a2 = Int('a2')
    d2 = Int('d2')
    a3 = Int('a3')
    d3 = Int('d3')

    # Constraints for durations
    solver.add(d1 - a1 + 1 == 2)
    solver.add(d2 - a2 + 1 == 2)
    solver.add(d3 - a3 + 1 == 5)

    # Arrival of next city is departure of previous
    solver.add(a2 == d1)
    solver.add(a3 == d2)

    # Last departure is day 7
    solver.add(d3 == 7)

    # Days are positive and ordered
    solver.add(a1 >= 1)
    solver.add(d1 <= 7)
    solver.add(a2 >= 1)
    solver.add(d2 <= 7)
    solver.add(a3 >= 1)
    solver.add(d3 <= 7)

    if solver.check() == sat:
        model = solver.model()
        a1_val = model[a1].as_long()
        d1_val = model[d1].as_long()
        a2_val = model[a2].as_long()
        d2_val = model[d2].as_long()
        a3_val = model[a3].as_long()
        d3_val = model[d3].as_long()

        itinerary = []
        # Riga: days a1 to d1-1
        for day in range(a1_val, d1_val):
            itinerary.append({"day": day, "city": "Riga"})
        # Amsterdam: days a2 to d2-1
        for day in range(a2_val, d2_val):
            itinerary.append({"day": day, "city": "Amsterdam"})
        # Mykonos: days a3 to d3
        for day in range(a3_val, d3_val + 1):
            itinerary.append({"day": day, "city": "Mykonos"})

        # Output the JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()