from z3 import *
import json

def main():
    cities = ["Venice", "Salzburg", "Stockholm", "Frankfurt", "Florence", "Barcelona", "Stuttgart"]
    city_to_int = {c: i for i, c in enumerate(cities)}
    n_days = 18
    bv_size = 3  # 3 bits can represent 0-7 (7 cities)

    # Create flight connection sets
    allowed_pairs = set()
    connections = [
        ("Barcelona", "Frankfurt"), ("Florence", "Frankfurt"),
        ("Stockholm", "Barcelona"), ("Barcelona", "Florence"),
        ("Venice", "Barcelona"), ("Stuttgart", "Barcelona"),
        ("Frankfurt", "Salzburg"), ("Stockholm", "Frankfurt"),
        ("Stuttgart", "Stockholm"), ("Stuttgart", "Frankfurt"),
        ("Venice", "Stuttgart"), ("Venice", "Frankfurt")
    ]
    for a, b in connections:
        i, j = city_to_int[a], city_to_int[b]
        allowed_pairs.add((i, j))
        allowed_pairs.add((j, i))

    # Flight validator function
    def valid_flight(i, j):
        return Or([And(i == a, j == b) for a, b in allowed_pairs])

    # Initialize solver
    s = Solver()
    
    # Bit-vector variables for start cities
    start_city = [BitVec(f'start_{d}', bv_size) for d in range(n_days)]
    flight = [Bool(f'flight_{d}') for d in range(n_days-1)]

    # Constraints
    s.add(start_city[0] == city_to_int["Venice"])  # Start in Venice
    
    # City domain constraints
    for t in range(n_days):
        s.add(ULT(start_city[t], 7))  # Ensure 0-6 range

    # Flight and continuity constraints
    for t in range(n_days-1):
        current = start_city[t]
        next_c = start_city[t+1]
        flight_taken = flight[t]
        
        s.add(If(flight_taken,
                 And(current != next_c, valid_flight(current, next_c)),
                 current == next_c))

    # City requirements
    reqs = [0] * 7
    reqs[city_to_int["Venice"]] = 5
    reqs[city_to_int["Salzburg"]] = 4
    reqs[city_to_int["Stockholm"]] = 2
    reqs[city_to_int["Frankfurt"]] = 4
    reqs[city_to_int["Florence"]] = 4
    reqs[city_to_int["Barcelona"]] = 2
    reqs[city_to_int["Stuttgart"]] = 3

    # Presence calculation
    for c in range(7):
        total = 0
        for t in range(n_days):
            if t < n_days-1:
                present = Or(start_city[t] == c, 
                             And(flight[t], start_city[t+1] == c))
            else:
                present = (start_city[t] == c)
            total += If(present, 1, 0)
        s.add(total == reqs[c])

    # Venice days 1-5 constraint
    for t in range(5):
        if t < n_days-1:
            in_venice = Or(start_city[t] == 0, 
                           And(flight[t], start_city[t+1] == 0))
        else:
            in_venice = (start_city[t] == 0)
        s.add(in_venice)

    # Solve and generate itinerary
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        for day in range(n_days):
            start_val = m.eval(start_city[day]).as_long()
            cities_today = {cities[start_val]}
            
            if day < n_days-1:
                if is_true(m.eval(flight[day])):
                    next_val = m.eval(start_city[day+1]).as_long()
                    cities_today.add(cities[next_val])
            
            itinerary.append({
                "day": day + 1,
                "cities": sorted(list(cities_today))
            })
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()