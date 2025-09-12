import z3
import json

def main():
    city_codes = {
        'Helsinki': 0,
        'Warsaw': 1,
        'Madrid': 2,
        'Split': 3,
        'Reykjavik': 4,
        'Budapest': 5
    }

    durations = {
        0: 2,  # Helsinki
        1: 3,  # Warsaw
        2: 4,  # Madrid
        3: 4,  # Split
        4: 2,  # Reykjavik
        5: 4   # Budapest
    }

    direct_flights = [
        ('Helsinki', 'Reykjavik'),
        ('Budapest', 'Warsaw'),
        ('Madrid', 'Split'),
        ('Helsinki', 'Split'),
        ('Helsinki', 'Madrid'),
        ('Helsinki', 'Budapest'),
        ('Reykjavik', 'Warsaw'),
        ('Helsinki', 'Warsaw'),
        ('Madrid', 'Budapest'),
        ('Budapest', 'Reykjavik'),
        ('Madrid', 'Warsaw'),
        ('Warsaw', 'Split'),
        ('Reykjavik', 'Madrid'),
    ]

    allowed_flights = set()
    for a, b in direct_flights:
        allowed_flights.add((city_codes[a], city_codes[b]))
        allowed_flights.add((city_codes[b], city_codes[a]))

    s = z3.Solver()

    # Order variables: first city is Helsinki (code 0)
    order = [0] + [z3.Int(f"order_{i}") for i in range(1, 6)]

    # Ensure remaining cities are distinct and in the allowed set
    s.add(z3.Distinct(order[1:]))
    for i in range(1, 6):
        s.add(z3.And(order[i] >= 1, order[i] <= 5))

    # Start day variables
    S = [z3.Int(f"S_{i}") for i in range(6)]
    s.add(S[0] == 1)

    for i in range(1, 6):
        prev_city = order[i - 1]
        duration_prev = z3.If(prev_city == 0, 2,
                              z3.If(prev_city == 1, 3,
                                    z3.If(prev_city == 2, 4,
                                          z3.If(prev_city == 3, 4,
                                                z3.If(prev_city == 4, 2,
                                                      z3.If(prev_city == 5, 4, 0))))))
        s.add(S[i] == S[i - 1] + duration_prev - 1)

    # Flight constraints between consecutive cities
    for i in range(1, 6):
        prev = order[i - 1]
        curr = order[i]
        constraints = []
        for a, b in allowed_flights:
            constraints.append(z3.And(prev == a, curr == b))
        s.add(z3.Or(*constraints))

    # Constraints for Warsaw and Reykjavik
    for i in range(6):
        # Warsaw constraint
        s.add(z3.Implies(order[i] == 1,
                         z3.Or(
                             z3.And(S[i] >= 9, S[i] <= 11),
                             z3.And(S[i] + 1 >= 9, S[i] + 1 <= 11),
                             z3.And(S[i] + 2 >= 9, S[i] + 2 <= 11)
                         )))
        # Reykjavik constraint
        s.add(z3.Implies(order[i] == 4,
                         z3.Or(
                             z3.And(S[i] >= 8, S[i] <= 9),
                             z3.And(S[i] + 1 >= 8, S[i] + 1 <= 9)
                         )))

    # Ensure total days is 14
    last_day = S[5] + z3.If(order[5] == 0, 2,
                            z3.If(order[5] == 1, 3,
                                  z3.If(order[5] == 2, 4,
                                        z3.If(order[5] == 3, 4,
                                              z3.If(order[5] == 4, 2,
                                                    z3.If(order[5] == 5, 4, 0))))) - 1
    s.add(last_day == 14)

    if s.check() == z3.sat:
        model = s.model()
        order_values = [model.evaluate(order[i]).as_long() for i in range(6)]
        S_values = [model.evaluate(S[i]).as_long() for i in range(6)]

        # Generate itinerary
        itinerary = []
        for i in range(6):
            city_code = order_values[i]
            city_name = [k for k, v in city_codes.items() if v == city_code][0]
            duration = durations[city_code]
            start_day = S_values[i]
            end_day = start_day + duration - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_name
            })

        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()