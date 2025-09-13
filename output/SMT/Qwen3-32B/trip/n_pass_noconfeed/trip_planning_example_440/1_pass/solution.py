from z3 import *

def main():
    # Define cities as integers
    SPLIT = 0
    HEL = 1
    REY = 2
    VIL = 3
    GEN = 4

    allowed_edges = {
        (SPLIT, HEL), (HEL, SPLIT),
        (SPLIT, GEN), (GEN, SPLIT),
        (SPLIT, VIL), (VIL, SPLIT),
        (HEL, GEN), (GEN, HEL),
        (HEL, REY), (REY, HEL),
        (HEL, VIL), (VIL, HEL),
    }

    # Create solver
    s = Solver()

    # Sequence variables: 5 cities
    sequence = [Int(f'city_{i}') for i in range(5)]

    # Constraints: all distinct (permutation)
    s.add(Distinct(sequence))

    # Constraints for allowed edges between consecutive cities
    for i in range(4):
        current = sequence[i]
        next_city = sequence[i+1]
        # Generate all allowed pairs for this transition
        allowed_pairs = []
        for a, b in allowed_edges:
            allowed_pairs.append(And(current == a, next_city == b))
        s.add(Or(allowed_pairs))

    # Durations for each city
    durations = {
        SPLIT: 2,
        HEL: 2,
        REY: 3,
        VIL: 3,
        GEN: 6,
    }

    # Start and end days for each city in the sequence
    start_days = [Int(f'start_{i}') for i in range(5)]
    end_days = [Int(f'end_{i}') for i in range(5)]

    # Constraints for start_days and end_days
    # start_days[0] = 1
    s.add(start_days[0] == 1)

    for i in range(1, 5):
        s.add(start_days[i] == end_days[i-1])

    for i in range(5):
        # duration_i depends on the city in sequence[i]
        d_i = If(sequence[i] == SPLIT, 2,
                 If(sequence[i] == HEL, 2,
                    If(sequence[i] == REY, 3,
                       If(sequence[i] == VIL, 3, 6))))
        s.add(end_days[i] == start_days[i] + d_i - 1)

    # The end day of the last city must be 12
    s.add(end_days[4] == 12)

    # Constraints for Reykjavik and Vilnius start days
    for i in range(5):
        s.add(Implies(sequence[i] == REY, start_days[i] == 10))
        s.add(Implies(sequence[i] == VIL, start_days[i] == 7))

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract the sequence of cities
        seq_values = [model.evaluate(city).as_long() for city in sequence]
        # Extract start_days and end_days
        start_values = [model.evaluate(start_days[i]).as_long() for i in range(5)]
        end_values = [model.evaluate(end_days[i]).as_long() for i in range(5)]

        # Map city integers to names
        city_names = {0: "Split", 1: "Helsinki", 2: "Reykjavik", 3: "Vilnius", 4: "Geneva"}

        # Build the itinerary
        itinerary = []
        for i in range(5):
            city = seq_values[i]
            start = start_values[i]
            end = end_values[i]
            day_range = f"Day {start}-{end}"
            city_name = city_names[city]
            itinerary.append({"day_range": day_range, "place": city_name})

        # Output as JSON
        import json
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()