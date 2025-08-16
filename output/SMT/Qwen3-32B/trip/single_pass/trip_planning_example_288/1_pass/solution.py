import json
from z3 import *

def main():
    solver = Solver()

    # Define variables for start and end days of each city
    start_M = Int('start_M')
    end_M = Int('end_M')
    start_D = Int('start_D')
    end_D = Int('end_D')
    start_V = Int('start_V')
    end_V = Int('end_V')
    start_S = Int('start_S')
    end_S = Int('end_S')

    # Constraints for Manchester and Stuttgart
    solver.add(start_M == 1)
    solver.add(end_M == 7)
    solver.add(start_S == 11)
    solver.add(end_S == 15)

    # Madrid duration is 4 days: end_D = start_D + 3
    solver.add(end_D == start_D + 3)

    # Vienna duration is 2 days: end_V = start_V + 1
    solver.add(end_V == start_V + 1)

    # Transitions between cities
    solver.add(start_D == end_M)  # M ends at 7, D starts at 7
    solver.add(start_V == end_D)  # V starts at end of D
    solver.add(start_S == end_V)  # S starts at end of V (which must be 11)

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()

        # Get the values for start and end of D and V
        start_D_val = model.evaluate(start_D).as_long()
        end_D_val = model.evaluate(end_D).as_long()
        start_V_val = model.evaluate(start_V).as_long()
        end_V_val = model.evaluate(end_V).as_long()

        # Initialize itinerary dictionary
        itinerary = {day: None for day in range(1, 16)}

        # Assign Manchester
        for day in range(1, end_M + 1):
            itinerary[day] = "Manchester"

        # Assign Madrid
        for day in range(start_D_val, end_D_val + 1):
            itinerary[day] = "Madrid"

        # Assign Vienna
        for day in range(start_V_val, end_V_val + 1):
            itinerary[day] = "Vienna"

        # Assign Stuttgart
        for day in range(start_S, end_S + 1):
            itinerary[day] = "Stuttgart"

        # Convert to list of day-place mappings
        itinerary_list = [{"day": day, "city": city} for day, city in itinerary.items()]

        # Output as JSON
        output = {"itinerary": itinerary_list}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()