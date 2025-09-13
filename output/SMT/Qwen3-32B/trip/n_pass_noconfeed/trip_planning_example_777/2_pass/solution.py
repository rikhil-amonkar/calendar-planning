import z3
import json

def main():
    cities = ['Reykjavik', 'Vienna', 'Helsinki', 'Riga', 'Tallinn', 'Dublin']
    durations_values = [2, 2, 3, 3, 5, 5]  # durations for each city in order

    direct_flights = [
        [False, True, True, False, False, True],  # Reykjavik
        [True, False, True, True, False, True],   # Vienna
        [True, True, False, True, True, True],    # Helsinki
        [False, True, True, False, True, True],   # Riga
        [False, False, True, True, False, True],  # Tallinn
        [True, True, True, True, True, False],    # Dublin
    ]

    s = z3.Solver()

    # Order variables: order[0] to order[5], each is 0-5 (city index)
    order = [z3.Int('order_{}'.format(i)) for i in range(6)]
    for i in range(6):
        s.add(z3.And(order[i] >= 0, order[i] <= 5))

    # All cities must be distinct
    s.add(z3.Distinct(order))

    # Start positions for each city in the order
    start_pos = [z3.Int('start_pos_{}'.format(i)) for i in range(6)]

    # Create a Z3 array for durations to allow symbolic indexing
    durations = z3.Array('durations', z3.IntSort(), z3.IntSort())
    for i in range(6):
        durations = z3.Store(durations, i, durations_values[i])

    # Constraints for start_pos based on order
    for i in range(5):
        s.add(start_pos[i+1] == start_pos[i] + durations[order[i]] - 1)

    # End day of last city is 15
    s.add(start_pos[5] + durations[order[5]] - 1 == 15)

    # Constraints for specific cities' start days
    vienna_idx = 1
    helsinki_idx = 2
    tallinn_idx = 4
    for i in range(6):
        s.add(z3.Implies(order[i] == vienna_idx, start_pos[i] == 2))
        s.add(z3.Implies(order[i] == helsinki_idx, start_pos[i] == 3))
        s.add(z3.Implies(order[i] == tallinn_idx, start_pos[i] == 7))

    # Direct flight constraints between consecutive cities
    for i in range(5):
        allowed = []
        for a in range(6):
            for b in range(6):
                if direct_flights[a][b]:
                    allowed.append(z3.And(order[i] == a, order[i+1] == b))
        s.add(z3.Or(allowed))

    # Check if the constraints are satisfiable
    if s.check() == z3.sat:
        model = s.model()
        order_values = [model[order[i]].as_long() for i in range(6)]
        start_pos_values = [model[start_pos[i]].as_long() for i in range(6)]
        itinerary = []
        for i in range(6):
            city_idx = order_values[i]
            city_name = cities[city_idx]
            start_day = start_pos_values[i]
            duration = durations_values[city_idx]
            end_day = start_day + duration - 1
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city_name})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()