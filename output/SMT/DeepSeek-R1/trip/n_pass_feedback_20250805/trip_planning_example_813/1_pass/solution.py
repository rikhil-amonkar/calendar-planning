from z3 import *
import json

def main():
    cities = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']
    n_cities = len(cities)
    Seville, Vilnius, Santorini, London, Stuttgart, Dublin, Frankfurt = range(n_cities)
    
    edges_set = set()
    pairs = [(Dublin, Frankfurt), (London, Frankfurt), (Dublin, London), 
             (Vilnius, Frankfurt), (Stuttgart, Frankfurt), (Seville, Dublin), 
             (Santorini, London), (Stuttgart, London), (Dublin, Santorini)]
    for (a, b) in pairs:
        if a < b:
            edges_set.add((a, b))
        else:
            edges_set.add((b, a))
    
    s = Solver()
    C = [Int(f'C_{i}') for i in range(1, 18)]
    
    for i in range(17):
        s.add(And(C[i] >= 0, C[i] < n_cities))
    
    req_days = {
        Seville: 5,
        Vilnius: 3,
        Santorini: 2,
        London: 2,
        Stuttgart: 3,
        Dublin: 3,
        Frankfurt: 5
    }
    
    for city in range(n_cities):
        count1 = 0
        for i in range(17):
            count1 += If(C[i] == city, 1, 0)
        count2 = 0
        for i in range(16):
            count2 += If(And(C[i] == city, C[i+1] != city), 1, 0)
        total = count1 + count2
        s.add(total == req_days[city])
    
    s.add(C[8] == London)
    s.add(C[9] == London)
    
    stuttgart_cond = []
    for d in [7, 8, 9]:
        idx = d - 1
        cond1 = (C[idx] == Stuttgart)
        if d > 1:
            cond2 = And(C[idx-1] == Stuttgart, C[idx] != Stuttgart)
            stuttgart_cond.append(Or(cond1, cond2))
        else:
            stuttgart_cond.append(cond1)
    s.add(Or(stuttgart_cond))
    
    for i in range(16):
        a = C[i]
        b = C[i+1]
        cond_list = []
        for edge in edges_set:
            a0, b0 = edge
            cond_list.append(And(a == a0, b == b0))
            cond_list.append(And(a == b0, b == a0))
        flight_ok = Or(a == b, Or(cond_list))
        s.add(flight_ok)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(17):
            city_val = m.evaluate(C[i])
            if city_val is not None:
                city_index = city_val.as_long()
                itinerary.append(cities[city_index])
        result = {
            "itinerary": [
                {"day": i+1, "place": itinerary[i]} for i in range(17)
            ]
        }
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()