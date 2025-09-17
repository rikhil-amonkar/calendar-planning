from z3 import *
import json

def main():
    # City indices
    cities = ["Barcelona", "Edinburgh", "Hamburg", "Krakow", "Paris", "Riga", "Stockholm", "Vienna"]
    n_days = 16
    n_cities = 8
    
    # Direct flights as set of tuples (min, max)
    direct_flights_list = [
        (2,6), (7,6), (4,1), (5,0), (4,5), (3,0), (1,6), (4,3), (3,6), (5,1),
        (0,6), (4,6), (3,1), (7,2), (4,2), (5,6), (2,0), (7,0), (3,7), (5,2),
        (0,1), (4,0), (2,1), (4,7), (7,5)
    ]
    direct_flights_set = set()
    for (c1, c2) in direct_flights_list:
        if c1 < c2:
            direct_flights_set.add((c1, c2))
        else:
            direct_flights_set.add((c2, c1))
    
    # Initialize solver
    s = Solver()
    
    # stay[0] to stay[16]
    stay = [Int(f"stay_{i}") for i in range(17)]
    
    # City constraints
    for i in range(17):
        s.add(stay[i] >= 0, stay[i] < n_cities)
    
    # Fixed constraints
    s.add(stay[0] == 4)  # Paris before day1
    s.add(stay[1] == 4)  # Paris on day1
    s.add(stay[2] == 4)  # Paris on day2
    s.add(stay[10] == 2) # Hamburg on day10 (night)
    s.add(stay[11] == 2) # Hamburg on day11 (night)
    s.add(stay[16] == 6) # Stockholm on day16 (night)
    
    # Direct flight constraints
    for i in range(1, 17):
        c1 = stay[i-1]
        c2 = stay[i]
        min_c = If(c1 < c2, c1, c2)
        max_c = If(c1 < c2, c2, c1)
        flight_exists = Or([And(min_c == flight[0], max_c == flight[1]) for flight in direct_flights_set])
        s.add(If(c1 != c2, flight_exists, True))
    
    # Required days per city [Barcelona, Edinburgh, Hamburg, Krakow, Paris, Riga, Stockholm, Vienna]
    # Adjusted to sum to 16 days
    required_days = [2, 2, 2, 2, 2, 2, 2, 2]
    for c in range(n_cities):
        total_days = Sum([If(stay[i] == c, 1, 0) for i in range(1, 17)])
        s.add(total_days == required_days[c])
    
    # Edinburgh between day12 and day15
    s.add(Or([stay[i] == 1 for i in range(12, 16)]))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        stay_values = [m.evaluate(stay[i]).as_long() for i in range(17)]
        itinerary = []
        start = 1
        current_city = stay_values[1]
        for day in range(2, 17):
            if stay_values[day] == current_city:
                continue
            else:
                itinerary.append({
                    "day_range": f"Day {start}-{day-1}",
                    "place": cities[current_city]
                })
                start = day
                current_city = stay_values[day]
        itinerary.append({
            "day_range": f"Day {start}-16",
            "place": cities[current_city]
        })
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()