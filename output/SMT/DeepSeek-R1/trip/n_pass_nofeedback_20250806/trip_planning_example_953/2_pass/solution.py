from z3 import *
import json

def main():
    # City mapping
    cities = ["Venice", "Salzburg", "Stockholm", "Frankfurt", "Florence", "Barcelona", "Stuttgart"]
    city_to_int = {c: i for i, c in enumerate(cities)}
    n_days = 18
    n_cities = 7

    # Direct flights (as tuples of city indices)
    given_edges = [
        ("Barcelona", "Frankfurt"),
        ("Florence", "Frankfurt"),
        ("Stockholm", "Barcelona"),
        ("Barcelona", "Florence"),
        ("Venice", "Barcelona"),
        ("Stuttgart", "Barcelona"),
        ("Frankfurt", "Salzburg"),
        ("Stockholm", "Frankfurt"),
        ("Stuttgart", "Stockholm"),
        ("Stuttgart", "Frankfurt"),
        ("Venice", "Stuttgart"),
        ("Venice", "Frankfurt")
    ]
    allowed_edges = set()
    for a, b in given_edges:
        i = city_to_int[a]
        j = city_to_int[b]
        allowed_edges.add((i, j))
        allowed_edges.add((j, i))
    allowed_edges_list = list(allowed_edges)

    # Create solver and variables
    s = Solver()
    start_city = [Int(f'start_city_{d+1}') for d in range(n_days)]
    flight = [Bool(f'flight_{d+1}') for d in range(n_days-1)]

    # Constraint: Day 1 starts in Venice (index 0)
    s.add(start_city[0] == 0)

    # Constraints for flights and city continuity
    for t in range(n_days-1):
        current = start_city[t]
        next_city = start_city[t+1]
        flight_taken = flight[t]
        edge_condition = Or([And(current == a, next_city == b) for (a, b) in allowed_edges_list])
        s.add(If(flight_taken, 
                 And(current != next_city, edge_condition),
                 current == next_city))

    # Total days per city
    total_days = [0] * n_cities
    for c in range(n_cities):
        for t in range(n_days):
            if t < n_days-1:
                in_city = Or(start_city[t] == c, And(flight[t], start_city[t+1] == c))
            else:
                in_city = (start_city[t] == c)
            total_days[c] += If(in_city, 1, 0)

    # Required days per city
    s.add(total_days[city_to_int["Venice"]] == 5)
    s.add(total_days[city_to_int["Salzburg"]] == 4)
    s.add(total_days[city_to_int["Stockholm"]] == 2)
    s.add(total_days[city_to_int["Frankfurt"]] == 4)
    s.add(total_days[city_to_int["Florence"]] == 4)
    s.add(total_days[city_to_int["Barcelona"]] == 2)
    s.add(total_days[city_to_int["Stuttgart"]] == 3)

    # Constraint: In Venice on days 1 to 5 (indices 0 to 4)
    for t in range(5):
        if t < n_days-1:
            in_venice = Or(start_city[t] == city_to_int["Venice"], And(flight[t], start_city[t+1] == city_to_int["Venice"]))
        else:
            in_venice = (start_city[t] == city_to_int["Venice"])
        s.add(in_venice)

    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for t in range(n_days):
            day = t + 1
            start_city_val = model[start_city[t]]
            start_city_idx = start_city_val.as_long()
            cities_today = set()
            cities_today.add(start_city_idx)
            if t < n_days-1:
                flight_taken = model[flight[t]]
                if is_true(flight_taken):
                    next_city_val = model[start_city[t+1]]
                    next_city_idx = next_city_val.as_long()
                    cities_today.add(next_city_idx)
            city_names = [cities[idx] for idx in cities_today]
            itinerary.append({"day": day, "cities": sorted(city_names)})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()