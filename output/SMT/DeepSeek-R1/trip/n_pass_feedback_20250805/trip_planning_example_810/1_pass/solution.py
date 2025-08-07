from z3 import *
import json

def main():
    cities = ["Berlin", "Nice", "Athens", "Stockholm", "Barcelona", "Vilnius", "Lyon"]
    n_days = 20
    n_cities = 7
    req_days = [3, 5, 5, 5, 2, 4, 2]  # Berlin, Nice, Athens, Stockholm, Barcelona, Vilnius, Lyon
    
    connections_list = [
        (1, 6), (3, 2), (1, 2), (0, 2), (0, 1), (0, 4), (0, 5),
        (4, 1), (2, 5), (0, 3), (1, 3), (4, 2), (4, 3), (4, 6)
    ]
    
    directed_connections = set()
    for (a, b) in connections_list:
        directed_connections.add((a, b))
        directed_connections.add((b, a))
    
    c = [Int('c_%d' % i) for i in range(n_days)]
    f = [Bool('f_%d' % i) for i in range(n_days - 1)]
    
    solver = Solver()
    
    for i in range(n_days):
        solver.add(And(c[i] >= 0, c[i] < n_cities))
    
    for i in range(n_days - 1):
        flight_options = []
        for (a, b) in directed_connections:
            flight_options.append(And(c[i] == a, c[i + 1] == b))
        solver.add(If(f[i], Or(flight_options), c[i] == c[i + 1]))
    
    solver.add(c[0] == 0)
    
    solver.add(Or(c[2] == 0, And(f[2], c[3] == 0)))
    
    barcelona_day3 = Or(c[2] == 4, And(f[2], c[3] == 4))
    barcelona_day4 = Or(c[3] == 4, And(f[3], c[4] == 4))
    solver.add(Or(barcelona_day3, barcelona_day4))
    
    lyon_day4 = Or(c[3] == 6, And(f[3], c[4] == 6))
    lyon_day5 = Or(c[4] == 6, And(f[4], c[5] == 6))
    solver.add(Or(lyon_day4, lyon_day5))
    
    for j in range(n_cities):
        total = 0
        for i in range(n_days):
            total += If(c[i] == j, 1, 0)
        for i in range(n_days - 1):
            total += If(And(f[i], c[i + 1] == j), 1, 0)
        solver.add(total == req_days[j])
    
    if solver.check() == sat:
        m = solver.model()
        itinerary_list = []
        for day in range(1, n_days + 1):
            idx = day - 1
            current_city_val = m.evaluate(c[idx])
            current_city_name = cities[current_city_val.as_long()]
            if day < n_days and m.evaluate(f[idx]):
                next_city_val = m.evaluate(c[idx + 1])
                next_city_name = cities[next_city_val.as_long()]
                itinerary_list.append({"day": day, "city": current_city_name})
                itinerary_list.append({"day": day, "city": next_city_name})
            else:
                itinerary_list.append({"day": day, "city": current_city_name})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()