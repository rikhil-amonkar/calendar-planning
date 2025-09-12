import json
from z3 import *

def main():
    solver = Solver()

    # Brussels has fixed start and end due to conference
    start_brussels = 1
    end_brussels = 2

    # Variables for other cities
    start_barca = Int('start_barca')
    end_barca = Int('end_barca')
    start_split = Int('start_split')
    end_split = Int('end_split')

    # Transition constraints between cities (start of next city = end of previous)
    solver.add(start_barca == end_brussels)  # Brussels → Barcelona
    solver.add(start_split == end_barca)    # Barcelona → Split

    # Duration constraints
    solver.add(end_brussels - start_brussels + 1 == 2)  # Brussels: 2 days
    solver.add(end_barca - start_barca + 1 == 7)        # Barcelona: 7 days
    solver.add(end_split - start_split + 1 == 5)        # Split: 5 days
    solver.add(end_split == 12)                         # Total trip duration: 12 days

    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        sb = model[start_barca].as_long()
        eb = model[end_barca].as_long()
        ss = model[start_split].as_long()
        es = model[end_split].as_long()

        # Construct itinerary
        itinerary = [
            {"day_range": f"Day {start_brussels}-{end_brussels}", "place": "Brussels"},
            {"day_range": f"Day {sb}-{eb}", "place": "Barcelona"},
            {"day_range": f"Day {ss}-{es}", "place": "Split"}
        ]

        # Output as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"error": "No solution found."}))

if __name__ == "__main__":
    main()