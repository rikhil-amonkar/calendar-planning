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
    start_city = [Int('start_city_%d' % (d+1)) for d in range(n_days)]
    flight = [Bool('flight_%d' % (d+1)) for d in range(n_days-1)]

    # Constraint: Day 1 starts in Venice (index 0)
    s.add(start_city[0] == 0)

    # Constraints for flights and city continuity
    for t in range(n_days-1):
        current = start_city[t]
        next_city = start_city[t+1]
        # Flight constraint: if flight[t] is True, then (current, next_city) must be in allowed_edges and current != next_city
        # Otherwise, current must equal next_city
        flight_taken = flight[t]
        edge_condition = Or([And(current == a, next_city == b) for (a, b) in allowed_edges_list])
        s.add(If(flight_taken, 
                 And(current != next_city, edge_condition),
                 current == next_city))

    # Presence for each city each day
    presence = [[None for _ in range(n_cities)] for _ in range(n_days)]
    for t in range(n_days):
        for c in range(n_cities):
            if t < n_days-1:
                # On day t, city c is present if: start_city[t] is c, or we fly to c on day t (so flight[t] and start_city[t+1]==c)
                presence[t][c] = Or(start_city[t] == c, And(flight[t], start_city[t+1] == c))
            else:
                presence[t][c] = (start_city[t] == c)

    # Total days per city
    total_days_per_city = [0] * n_cities
    for c in range(n_cities):
        total = 0
        for t in range(n_days):
            total += If(presence[t][c], 1, 0)
        total_days_per_city[c] = total

    # Required days per city
    s.add(total_days_per_city[city_to_int["Venice"]] == 5)
    s.add(total_days_per_city[city_to_int["Salzburg"]] == 4)
    s.add(total_days_per_city[city_to_int["Stockholm"]] == 2)
    s.add(total_days_per_city[city_to_int["Frankfurt"]] == 4)
    s.add(total_days_per_city[city_to_int["Florence"]] == 4)
    s.add(total_days_per_city[city_to_int["Barcelona"]] == 2)
    s.add(total_days_per_city[city_to_int["Stuttgart"]] == 3)

    # Constraint: In Venice on days 1 to 5 (indices 0 to 4)
    for t in range(5):
        s.add(presence[t][city_to_int["Venice"]] == True)

    # Check and get model
    if s.check() == sat:
        model = s.model()
        start_city_vals = [model.eval(start_city[d]).as_long() for d in range(n_days)]
        flight_vals = [model.eval(flight[d]) for d in range(n_days-1)]
        
        itinerary = []
        for t in range(n_days):
            day = t + 1
            cities_today = set()
            # Add start city of the day
            cities_today.add(start_city_vals[t])
            # If flight on this day, add the destination (which is the start city of next day)
            if t < n_days-1 and is_true(flight_vals[t]):
                cities_today.add(start_city_vals[t+1])
            city_names = [cities[idx] for idx in cities_today]
            itinerary.append({"day": day, "cities": sorted(city_names)})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()