from z3 import *

def main():
    # Define city indices
    Bucharest, Warsaw, Stuttgart, Copenhagen, Dubrovnik = 0, 1, 2, 3, 4
    names = {
        Bucharest: "Bucharest",
        Warsaw: "Warsaw",
        Stuttgart: "Stuttgart",
        Copenhagen: "Copenhagen",
        Dubrovnik: "Dubrovnik"
    }
    req = [6, 2, 7, 3, 5]  # days required per city

    # Define flight edges (undirected)
    edges = [
        (Warsaw, Copenhagen),
        (Stuttgart, Copenhagen),
        (Warsaw, Stuttgart),
        (Bucharest, Copenhagen),
        (Bucharest, Warsaw),
        (Copenhagen, Dubrovnik)
    ]
    # Make edges bidirectional
    edges += [(j, i) for (i, j) in edges]

    # Initialize Z3 variables
    c1, c2, c3, c4, c5 = Ints('c1 c2 c3 c4 c5')
    e1, e2, e3, e4 = Ints('e1 e2 e3 e4')
    stuttgart_stay = Int('stuttgart_stay')
    bucharest_stay = Int('bucharest_stay')
    s = Solver()

    # City assignments (0-4)
    for c in [c1, c2, c3, c4, c5]:
        s.add(c >= 0, c <= 4)
    s.add(Distinct(c1, c2, c3, c4, c5))

    # Day constraints
    s.add(e1 == req[c1])
    s.add(e2 == e1 + req[c2] - 1)
    s.add(e3 == e2 + req[c3] - 1)
    s.add(e4 == e3 + req[c4] - 1)
    s.add(e4 == 20 - req[c5])  # e4 = 20 - last city's required days
    s.add(e1 >= 1, e1 < e2, e2 < e3, e3 < e4, e4 <= 19)

    # Stuttgart constraints (must start on day 7)
    s.add(stuttgart_stay >= 1, stuttgart_stay <= 5)
    s.add(Or(
        And(stuttgart_stay == 1, c1 == Stuttgart),
        And(stuttgart_stay == 2, c2 == Stuttgart),
        And(stuttgart_stay == 3, c3 == Stuttgart),
        And(stuttgart_stay == 4, c4 == Stuttgart),
        And(stuttgart_stay == 5, c5 == Stuttgart)
    ))
    start_stuttgart = Int('start_stuttgart')
    s.add(If(stuttgart_stay == 1, start_stuttgart == 1,
          If(stuttgart_stay == 2, start_stuttgart == e1,
          If(stuttgart_stay == 3, start_stuttgart == e2,
          If(stuttgart_stay == 4, start_stuttgart == e3,
          start_stuttgart == e4)))))
    s.add(start_stuttgart == 7)

    # Bucharest constraints (must start by day 6)
    s.add(bucharest_stay >= 1, bucharest_stay <= 5)
    s.add(Or(
        And(bucharest_stay == 1, c1 == Bucharest),
        And(bucharest_stay == 2, c2 == Bucharest),
        And(bucharest_stay == 3, c3 == Bucharest),
        And(bucharest_stay == 4, c4 == Bucharest),
        And(bucharest_stay == 5, c5 == Bucharest)
    ))
    start_bucharest = Int('start_bucharest')
    s.add(If(bucharest_stay == 1, start_bucharest == 1,
          If(bucharest_stay == 2, start_bucharest == e1,
          If(bucharest_stay == 3, start_bucharest == e2,
          If(bucharest_stay == 4, start_bucharest == e3,
          start_bucharest == e4)))))
    s.add(start_bucharest <= 6)

    # Flight connections
    s.add(Or([And(c1 == i, c2 == j) for (i, j) in edges]))
    s.add(Or([And(c2 == i, c3 == j) for (i, j) in edges]))
    s.add(Or([And(c3 == i, c4 == j) for (i, j) in edges]))
    s.add(Or([And(c4 == i, c5 == j) for (i, j) in edges]))

    # Check and get model
    if s.check() == sat:
        m = s.model()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        c4_val = m[c4].as_long()
        c5_val = m[c5].as_long()
        e1_val = m[e1].as_long()
        e2_val = m[e2].as_long()
        e3_val = m[e3].as_long()
        e4_val = m[e4].as_long()

        itinerary = []
        # Stay 1: from day 1 to e1_val
        itinerary.append({"day_range": f"Day 1-{e1_val}", "place": names[c1_val]})
        itinerary.append({"day_range": f"Day {e1_val}", "place": names[c1_val]})  # Departure
        itinerary.append({"day_range": f"Day {e1_val}", "place": names[c2_val]})  # Arrival
        itinerary.append({"day_range": f"Day {e1_val}-{e2_val}", "place": names[c2_val]})

        # Stay 2: from e1_val to e2_val
        itinerary.append({"day_range": f"Day {e2_val}", "place": names[c2_val]})  # Departure
        itinerary.append({"day_range": f"Day {e2_val}", "place": names[c3_val]})  # Arrival
        itinerary.append({"day_range": f"Day {e2_val}-{e3_val}", "place": names[c3_val]})

        # Stay 3: from e2_val to e3_val
        itinerary.append({"day_range": f"Day {e3_val}", "place": names[c3_val]})  # Departure
        itinerary.append({"day_range": f"Day {e3_val}", "place": names[c4_val]})  # Arrival
        itinerary.append({"day_range": f"Day {e3_val}-{e4_val}", "place": names[c4_val]})

        # Stay 4: from e3_val to e4_val
        itinerary.append({"day_range": f"Day {e4_val}", "place": names[c4_val]})  # Departure
        itinerary.append({"day_range": f"Day {e4_val}", "place": names[c5_val]})  # Arrival
        itinerary.append({"day_range": f"Day {e4_val}-19", "place": names[c5_val]})

        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()