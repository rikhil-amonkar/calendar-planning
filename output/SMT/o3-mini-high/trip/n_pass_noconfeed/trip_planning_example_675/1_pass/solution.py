import json
from z3 import *

def main():
    # Mapping of cities to IDs:
    # 0: Dubrovnik, 1: Split, 2: Milan, 3: Porto, 4: Krakow, 5: Munich
    city_names = {
        0: "Dubrovnik",
        1: "Split",
        2: "Milan",
        3: "Porto",
        4: "Krakow",
        5: "Munich"
    }
    # Fixed durations for each city
    durations_fixed = {0: 4, 1: 3, 2: 3, 3: 4, 4: 2, 5: 5}

    # Allowed direct flights (both directions)
    allowed_edges = [
        (0, 5), (5, 0),     # Dubrovnik <-> Munich
        (1, 2), (2, 1),     # Split <-> Milan
        (2, 3), (3, 2),     # Milan <-> Porto
        (5, 4), (4, 5),     # Munich <-> Krakow
        (5, 2), (2, 5),     # Munich <-> Milan
        (4, 1), (1, 4),     # Krakow <-> Split
        (4, 2), (2, 4),     # Krakow <-> Milan
        (5, 1), (1, 5),     # Munich <-> Split
        (5, 3), (3, 5)      # Munich <-> Porto
    ]

    # Define a helper function to get duration based on city ID.
    # This is a Z3 expression: if city==0 then 4, etc.
    def duration(city):
        return If(city == 0, 4,
               If(city == 1, 3,
               If(city == 2, 3,
               If(city == 3, 4,
               If(city == 4, 2, 5)))))

    # Create the solver instance.
    solver = Solver()

    # Define decision variables:
    # order[i] will be the city ID visited at the i-th segment (0-indexed)
    order = [Int("o%d" % i) for i in range(6)]
    # s[i] will be the start day of the i-th segment.
    s = [Int("s%d" % i) for i in range(6)]

    # Constraint: each order[i] must be in 0..5 and all must be distinct (permutation)
    for i in range(6):
        solver.add(order[i] >= 0, order[i] <= 5)
    solver.add(Distinct(order))

    # Set starting day for the very first city to be day 1.
    solver.add(s[0] == 1)

    # Sequential scheduling: if you are in city at segment i, and you fly on the last day,
    # then the next city starts on the same flight day.
    # s[i+1] = s[i] + duration(order[i]) - 1 for i=0..4
    for i in range(5):
        solver.add(s[i+1] == s[i] + duration(order[i]) - 1)

    # Total itinerary: Last day in the last city is s[5] + duration(order[5]) - 1 = 16.
    solver.add(s[5] + duration(order[5]) - 1 == 16)

    # Flight connectivity: For each leg, the transition must be via a direct flight.
    for i in range(5):
        a = order[i]
        b = order[i+1]
        conn_options = []
        for (src, dst) in allowed_edges:
            conn_options.append(And(a == src, b == dst))
        solver.add(Or(conn_options))

    # Event constraints.
    # Wedding in Milan (city 2) must occur between day 11 and 13.
    # Milan's segment is [s, s+2] so we require s <= 13 and s+2 >= 11.
    for i in range(6):
        solver.add(Implies(order[i] == 2, And(s[i] <= 13, s[i] + 2 >= 11)))

    # Annual show in Munich (city 5) from day 4 to 8:
    # Munich's segment is [s, s+4]. To attend the show, we require that s <= 8.
    for i in range(6):
        solver.add(Implies(order[i] == 5, s[i] <= 8))

    # Meet friends in Krakow (city 4) between day 8 and 9:
    # Krakow's segment is [s, s+1]. We need s <= 9 and s+1 >= 8.
    for i in range(6):
        solver.add(Implies(order[i] == 4, And(s[i] <= 9, s[i] + 1 >= 8)))

    # Check the model and extract itinerary.
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        for i in range(6):
            city_id = m.evaluate(order[i]).as_long()
            start_day = m.evaluate(s[i]).as_long()
            dur = durations_fixed[city_id]
            end_day = start_day + dur - 1
            itinerary.append({
                "day_range": "Day {}-{}".format(start_day, end_day),
                "place": city_names[city_id]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()