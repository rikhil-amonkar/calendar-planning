from z3 import *
import json

def main():
    solver = Solver()

    # Variables for cities (0: Dublin, 1: Riga, 2: Vilnius)
    city_1, city_2, city_3 = Ints('city_1 city_2 city_3')
    end_1, end_2 = Ints('end_1 end_2')

    # All three cities must be distinct
    solver.add(Distinct(city_1, city_2, city_3))

    # Transition constraints between city_1 and city_2
    solver.add(Implies(city_1 == 0, city_2 == 1))
    solver.add(Implies(city_1 == 1, Or(city_2 == 0, city_2 == 2)))
    solver.add(Implies(city_1 == 2, False))  # No allowed transitions from Vilnius as first city

    # Transition constraints between city_2 and city_3
    solver.add(Implies(city_2 == 0, city_3 == 1))
    solver.add(Implies(city_2 == 1, Or(city_3 == 0, city_3 == 2)))
    solver.add(Implies(city_2 == 2, False))  # No allowed transitions from Vilnius as second city

    # Constraints for end_1 based on city_1
    solver.add(Or(
        And(city_1 == 0, end_1 == 2),
        And(city_1 == 1, end_1 == 5),
        And(city_1 == 2, end_1 == 7)
    ))

    # Constraints for end_2 based on city_2 and end_1
    solver.add(Or(
        And(city_2 == 0, end_2 == end_1 + 1),
        And(city_2 == 1, end_2 == end_1 + 4),
        And(city_2 == 2, end_2 == end_1 + 6)
    ))

    # Constraints for city_3's end_3 == 12
    solver.add(Or(
        And(city_3 == 0, end_2 + 1 == 12),
        And(city_3 == 1, end_2 + 4 == 12),
        And(city_3 == 2, end_2 + 6 == 12)
    ))

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        c1 = model[city_1].as_long()
        c2 = model[city_2].as_long()
        c3 = model[city_3].as_long()
        e1 = model[end_1].as_long()
        e2 = model[end_2].as_long()

        # Generate the itinerary
        itinerary = []
        city_map = {0: "Dublin", 1: "Riga", 2: "Vilnius"}
        start_1 = 1
        day_range_1 = f"Day {start_1}-{e1}"
        itinerary.append({"day_range": day_range_1, "place": city_map[c1]})

        start_2 = e1
        day_range_2 = f"Day {start_2}-{e2}"
        itinerary.append({"day_range": day_range_2, "place": city_map[c2]})

        start_3 = e2
        day_range_3 = f"Day {start_3}-12"
        itinerary.append({"day_range": day_range_3, "place": city_map[c3]})

        # Output as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()