import json
from z3 import *

def main():
    cities = ['Venice', 'Barcelona', 'Copenhagen', 'Lyon', 'Reykjavik', 'Dubrovnik', 'Athens', 'Tallinn', 'Munich']
    durations = [4, 3, 4, 4, 4, 5, 2, 5, 3]
    
    edges_str = [
        "Copenhagen and Athens", 
        "Copenhagen and Dubrovnik", 
        "Munich and Tallinn", 
        "Copenhagen and Munich", 
        "Venice and Munich", 
        "from Reykjavik to Athens", 
        "Athens and Dubrovnik", 
        "Venice and Athens", 
        "Lyon and Barcelona", 
        "Copenhagen and Reykjavik", 
        "Reykjavik and Munich", 
        "Athens and Munich", 
        "Lyon and Munich", 
        "Barcelona and Reykjavik", 
        "Venice and Copenhagen", 
        "Barcelona and Dubrovnik", 
        "Lyon and Venice", 
        "Dubrovnik and Munich", 
        "Barcelona and Athens", 
        "Copenhagen and Barcelona", 
        "Venice and Barcelona", 
        "Barcelona and Munich", 
        "Barcelona and Tallinn", 
        "Copenhagen and Tallinn"
    ]
    
    unordered_edges = set()
    for s in edges_str:
        clean_s = s.replace("from ", "").replace(" to ", " and ").strip()
        parts = clean_s.split(' and ')
        if len(parts) < 2:
            continue
        city1 = parts[0].strip()
        city2 = parts[1].strip()
        try:
            idx1 = cities.index(city1)
            idx2 = cities.index(city2)
        except:
            continue
        if idx1 < idx2:
            edge = (idx1, idx2)
        else:
            edge = (idx2, idx1)
        unordered_edges.add(edge)
    
    s = Solver()
    
    order = [Int('order_%d' % i) for i in range(9)]
    start = [Int('start_%d' % i) for i in range(9)]
    
    s.add(Distinct(order))
    for i in range(9):
        s.add(order[i] >= 0, order[i] < 9)
    
    s.add(start[0] == 1)
    for i in range(1, 9):
        s.add(start[i] == start[i-1] + durations[order[i-1]] - 1)
    
    for i in range(9):
        s.add(If(order[i] == 1, And(start[i] >= 8, start[i] <= 12), True))
        s.add(If(order[i] == 2, And(start[i] >= 4, start[i] <= 10), True))
        s.add(If(order[i] == 5, And(start[i] >= 12, start[i] <= 20), True))
    
    for i in range(8):
        constraints = []
        for edge in unordered_edges:
            a, b = edge
            c1 = And(order[i] == a, order[i+1] == b)
            c2 = And(order[i] == b, order[i+1] == a)
            constraints.append(Or(c1, c2))
        s.add(Or(constraints))
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(9)]
        start_val = [0] * 9
        start_val[0] = 1
        for i in range(1, 9):
            prev_city_index = order_val[i-1]
            start_val[i] = start_val[i-1] + durations[prev_city_index] - 1
        
        itinerary = []
        for d in range(1, 27):
            places = []
            for pos in range(9):
                city_index = order_val[pos]
                s_day = start_val[pos]
                e_day = s_day + durations[city_index] - 1
                if s_day <= d <= e_day:
                    places.append(cities[city_index])
            itinerary.append({"day": d, "place": places})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()