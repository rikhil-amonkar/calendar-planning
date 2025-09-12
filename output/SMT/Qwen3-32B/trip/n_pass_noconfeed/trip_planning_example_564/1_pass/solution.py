import json
from z3 import *

def main():
    # Define cities as integers: 0=Istanbul, 1=Rome, 2=Seville, 3=Naples, 4=Santorini
    c1, c2, c3, c4, c5 = Ints('c1 c2 c3 c4 c5')
    s = Solver()

    # All cities are distinct
    s.add(Distinct(c1, c2, c3, c4, c5))

    # c5 is Santorini (4)
    s.add(c5 == 4)

    # Allowed transitions
    allowed_transitions = [
        (1, 4), (4, 1),  # Rome and Santorini
        (2, 1), (1, 2),  # Seville and Rome
        (0, 3), (3, 0),  # Istanbul and Naples
        (3, 4), (4, 3),  # Naples and Santorini
        (1, 3), (3, 1),  # Rome and Naples
        (1, 0), (0, 1),  # Rome and Istanbul
    ]

    # Check transitions between consecutive cities
    def is_allowed_transition(a, b):
        return Or([And(a == src, b == dst) for src, dst in allowed_transitions])

    s.add(is_allowed_transition(c1, c2))
    s.add(is_allowed_transition(c2, c3))
    s.add(is_allowed_transition(c3, c4))
    s.add(is_allowed_transition(c4, c5))

    # Define durations for each city in the sequence
    d1 = If(c1 == 0, 2, If(c1 == 1, 3, If(c1 == 2, 4, If(c1 == 3, 7, 4))))
    d2 = If(c2 == 0, 2, If(c2 == 1, 3, If(c2 == 2, 4, If(c2 == 3, 7, 4))))
    d3 = If(c3 == 0, 2, If(c3 == 1, 3, If(c3 == 2, 4, If(c3 == 3, 7, 4))))
    d4 = If(c4 == 0, 2, If(c4 == 1, 3, If(c4 == 2, 4, If(c4 == 3, 7, 4))))
    d5 = 4  # since c5 is 4 (Santorini)

    # Constraints for Istanbul's start day
    s.add(Or(c2 != 0, And(d1 >= 5, d1 <= 7)))
    s.add(Or(c3 != 0, And(d1 + d2 - 1 >= 5, d1 + d2 - 1 <= 7)))
    s.add(Or(c4 != 0, And(d1 + d2 + d3 - 2 >= 5, d1 + d2 + d3 - 2 <= 7)))
    s.add(c1 != 0)  # Istanbul cannot be in position 1

    if s.check() == sat:
        model = s.model()
        cities = [model.eval(c1), model.eval(c2), model.eval(c3), model.eval(c4), model.eval(c5)]
        cities = [int(cities[0]), int(cities[1]), int(cities[2]), int(cities[3]), int(cities[4])]

        # Compute durations for each city in the sequence
        durations = []
        for city in cities:
            if city == 0:
                durations.append(2)
            elif city == 1:
                durations.append(3)
            elif city == 2:
                durations.append(4)
            elif city == 3:
                durations.append(7)
            elif city == 4:
                durations.append(4)
        d1_val, d2_val, d3_val, d4_val, d5_val = durations

        # Compute start and end days
        start_days = [1]
        end_days = [start_days[0] + durations[0] - 1]
        for i in range(1, 5):
            start_days.append(end_days[i - 1])
            end_days.append(start_days[i] + durations[i] - 1)

        # Build the itinerary
        itinerary = []
        city_names = {0: "Istanbul", 1: "Rome", 2: "Seville", 3: "Naples", 4: "Santorini"}
        for i in range(5):
            start = start_days[i]
            end = end_days[i]
            city = city_names[cities[i]]
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})

        # Output as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()