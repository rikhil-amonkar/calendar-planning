import json
from z3 import *

def main():
    # City indices
    V, B, C, L, R, D, A, T, M = 0, 1, 2, 3, 4, 5, 6, 7, 8
    durs = [4, 3, 4, 4, 4, 5, 2, 5, 3]
    city_names = {
        V: "Venice",
        B: "Barcelona",
        C: "Copenhagen",
        L: "Lyon",
        R: "Reykjavik",
        D: "Dubrovnik",
        A: "Athens",
        T: "Tallinn",
        M: "Munich"
    }
    
    direct_flights = [
        (C, A), (C, D), (M, T), (C, M), (V, M), (R, A), (A, D), (V, A), (L, B), (C, R),
        (R, M), (A, M), (L, M), (B, R), (B, D), (B, A), (C, B), (V, C), (V, B), (B, M),
        (B, T), (C, T)
    ]
    direct_flights_set = set()
    for (x, y) in direct_flights:
        direct_flights_set.add((x, y))
        direct_flights_set.add((y, x))
    
    s = Solver()
    
    order = [Int('order_%d' % i) for i in range(9)]
    for i in range(9):
        s.add(And(order[i] >= 0, order[i] < 9))
    s.add(Distinct(order))
    
    arrival = [Int('arrival_%d' % i) for i in range(9)]
    
    s.add(arrival[order[0]] == 1)
    
    for i in range(1, 9):
        prev_city = order[i-1]
        curr_city = order[i]
        s.add(arrival[curr_city] == arrival[prev_city] + durs[prev_city] - 1)
    
    last_city = order[8]
    s.add(arrival[last_city] + durs[last_city] - 1 == 26)
    
    s.add(arrival[B] >= 9, arrival[B] <= 12)
    s.add(arrival[C] >= 4, arrival[C] <= 10)
    s.add(arrival[D] >= 12, arrival[D] <= 20)
    
    for i in range(1, 9):
        city_i = order[i-1]
        city_j = order[i]
        constraints = []
        for (x, y) in direct_flights_set:
            constraints.append(And(city_i == x, city_j == y))
        s.add(Or(constraints))
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(9)]
        arrival_val = [m.evaluate(arrival[i]).as_long() for i in range(9)]
        
        segments = []
        for i in range(9):
            city_index = order_val[i]
            start = arrival_val[city_index]
            end = start + durs[city_index] - 1
            segments.append((start, end, city_names[city_index]))
        
        itinerary = []
        for start, end, city in segments:
            itinerary.append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()