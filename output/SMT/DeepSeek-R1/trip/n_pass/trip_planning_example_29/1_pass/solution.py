from z3 import *
import json

def main():
    D = 0
    F = 1
    K = 2
    city_names = {D: "Dubrovnik", F: "Frankfurt", K: "Krakow"}
    
    start = [Int('start_%d' % i) for i in range(1, 12)]
    flight = [Bool('flight_%d' % i) for i in range(1, 11)]
    
    s = Solver()
    
    for i in range(11):
        s.add(Or(start[i] == D, start[i] == F, start[i] == K))
    
    allowed_edges = [(F, K), (K, F), (D, F), (F, D)]
    for i in range(10):
        edge_constraint = Or([And(start[i] == a, start[i+1] == b) for (a, b) in allowed_edges])
        s.add(If(flight[i], edge_constraint, start[i+1] == start[i]))
    
    in_cities = {D: [], F: [], K: []}
    for i in range(10):
        in_cities[D].append(Or(start[i] == D, And(flight[i], start[i+1] == D)))
        in_cities[F].append(Or(start[i] == F, And(flight[i], start[i+1] == F)))
        in_cities[K].append(Or(start[i] == K, And(flight[i], start[i+1] == K)))
    
    for i in range(8):
        s.add(Not(in_cities[K][i]))
    s.add(in_cities[K][8])
    s.add(in_cities[K][9])
    
    total_D = Sum([If(in_cities[D][i], 1, 0) for i in range(10)])
    s.add(total_D == 7)
    
    total_F = Sum([If(in_cities[F][i], 1, 0) for i in range(10)])
    s.add(total_F == 3)
    
    total_flights = Sum([If(flight[i], 1, 0) for i in range(10)])
    s.add(total_flights == 2)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(10):
            cities_today = []
            if is_true(m.eval(in_cities[D][day])):
                cities_today.append(city_names[D])
            if is_true(m.eval(in_cities[F][day])):
                cities_today.append(city_names[F])
            if is_true(m.eval(in_cities[K][day])):
                cities_today.append(city_names[K])
            cities_today.sort()
            place_str = ", ".join(cities_today)
            itinerary.append({"day": day+1, "place": place_str})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()