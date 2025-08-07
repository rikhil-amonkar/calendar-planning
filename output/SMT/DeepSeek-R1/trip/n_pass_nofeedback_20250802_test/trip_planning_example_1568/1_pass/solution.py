from z3 import *
import json

def main():
    n_days = 20
    n_cities = 10
    city_names = {
        0: "Prague",
        1: "Brussels",
        2: "Riga",
        3: "Munich",
        4: "Seville",
        5: "Stockholm",
        6: "Istanbul",
        7: "Amsterdam",
        8: "Vienna",
        9: "Split"
    }
    required_days = [5, 2, 2, 2, 3, 2, 2, 3, 5, 3]  # for cities 0 to 9

    edges = [
        (2, 5), (5, 1), (6, 3), (6, 2), (0, 9), (8, 1), (8, 2), (9, 5), (3, 7), (9, 7),
        (7, 5), (7, 2), (8, 5), (8, 6), (8, 4), (6, 7), (3, 1), (0, 3), (2, 3), (0, 7),
        (0, 1), (0, 6), (6, 5), (8, 0), (3, 9), (8, 7), (0, 5), (1, 4), (3, 5), (6, 1),
        (7, 4), (8, 9), (3, 4), (2, 1), (0, 2), (8, 3),
        # Adding symmetric edges
        (5, 2), (1, 5), (3, 6), (2, 6), (9, 0), (1, 8), (2, 8), (5, 9), (7, 3), (7, 9),
        (5, 7), (2, 7), (5, 8), (6, 8), (4, 8), (7, 6), (1, 3), (3, 0), (3, 2), (7, 0),
        (1, 0), (6, 0), (5, 6), (0, 8), (9, 3), (7, 8), (5, 0), (4, 1), (5, 3), (1, 6),
        (4, 7), (9, 8), (4, 3), (1, 2), (2, 0), (3, 8)
    ]
    allowed_edges = set(edges)

    s = Solver()
    city_day = [Int(f'city_day_{i}') for i in range(n_days)]
    for i in range(n_days):
        s.add(And(city_day[i] >= 0, city_day[i] < n_cities))
    
    transitions = []
    for i in range(n_days - 1):
        t = If(city_day[i] != city_day[i+1], 1, 0)
        transitions.append(t)
    s.add(sum(transitions) == 12)
    
    for i in range(n_days - 1):
        edge_cond = Or([And(city_day[i] == a, city_day[i+1] == b) for (a, b) in allowed_edges])
        s.add(If(city_day[i] != city_day[i+1], edge_cond, True))
    
    for c in range(n_cities):
        count1 = Sum([If(city_day[i] == c, 1, 0) for i in range(n_days)])
        count2 = Sum([If(And(city_day[i] != city_day[i+1], city_day[i+1] == c), 1, 0) for i in range(n_days - 1)])
        s.add(count1 + count2 == required_days[c])
    
    for d in [4, 5, 6, 7, 8]:
        cond = Or(city_day[d] == 0, And(d < n_days-1, city_day[d] != city_day[d+1], city_day[d+1] == 0))
        s.add(cond)
    
    cond16 = Or(city_day[15] == 5, And(city_day[15] != city_day[16], city_day[16] == 5))
    s.add(cond16)
    cond17 = Or(city_day[16] == 5, And(city_day[16] != city_day[17], city_day[17] == 5))
    s.add(cond17)
    
    cond15_riga = Or(city_day[14] == 2, And(city_day[14] != city_day[15], city_day[15] == 2))
    cond16_riga = Or(city_day[15] == 2, And(city_day[15] != city_day[16], city_day[16] == 2))
    s.add(Or(cond15_riga, cond16_riga))
    
    vienna_conds = []
    for d in range(0, 5):
        cond = Or(city_day[d] == 8, And(d < n_days-1, city_day[d] != city_day[d+1], city_day[d+1] == 8))
        vienna_conds.append(cond)
    s.add(Or(vienna_conds))
    
    split_conds = []
    for d in [10, 11, 12]:
        cond = Or(city_day[d] == 9, And(d < n_days-1, city_day[d] != city_day[d+1], city_day[d+1] == 9))
        split_conds.append(cond)
    s.add(Or(split_conds))
    
    if s.check() == sat:
        m = s.model()
        sol_city_day = [m.evaluate(city_day[i]).as_long() for i in range(n_days)]
        
        itinerary = []
        for day in range(1, n_days + 1):
            idx = day - 1
            if day < n_days and sol_city_day[idx] != sol_city_day[idx + 1]:
                places = [city_names[sol_city_day[idx]], city_names[sol_city_day[idx + 1]]]
            else:
                places = [city_names[sol_city_day[idx]]]
            itinerary.append({"day": day, "place": places})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()