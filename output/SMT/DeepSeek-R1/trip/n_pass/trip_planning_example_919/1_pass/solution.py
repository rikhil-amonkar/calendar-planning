from z3 import *
import json

def main():
    # City indices and lengths
    city_index = {
        "Vienna": 0,
        "Milan": 1,
        "Rome": 2,
        "Riga": 3,
        "Lisbon": 4,
        "Vilnius": 5,
        "Oslo": 6
    }
    index_to_city = {v: k for k, v in city_index.items()}
    length_dict = {
        0: 4,  # Vienna
        1: 2,  # Milan
        2: 3,  # Rome
        3: 2,  # Riga
        4: 3,  # Lisbon
        5: 4,  # Vilnius
        6: 3   # Oslo
    }
    
    # Middle stay variables
    s1, s2, s3, s4 = Ints('s1 s2 s3 s4')
    solver = Solver()
    
    # Domain constraints: middle cities are Milan, Rome, Riga, Vilnius (indices 1,2,3,5)
    domain = [1, 2, 3, 5]
    solver.add(Distinct(s1, s2, s3, s4))
    for var in [s1, s2, s3, s4]:
        solver.add(Or([var == d for d in domain]))
    
    # Allowed directed flights between middle cities
    allowed_middle = [(1,3), (1,5), (2,3), (3,1), (3,5), (5,1)]
    
    # Flight constraints
    solver.add(Or([And(s1 == u, s2 == v) for (u, v) in allowed_middle]))
    solver.add(Or([And(s2 == u, s3 == v) for (u, v) in allowed_middle]))
    solver.add(Or([And(s3 == u, s4 == v) for (u, v) in allowed_middle]))
    solver.add(Or(s4 == 1, s4 == 2, s4 == 3))  # Flight from last middle city to Lisbon must be allowed
    
    if solver.check() == sat:
        model = solver.model()
        s1_val = model[s1].as_long()
        s2_val = model[s2].as_long()
        s3_val = model[s3].as_long()
        s4_val = model[s4].as_long()
        
        # Full stay sequence: Vienna, middle cities, Lisbon, Oslo
        stay_city = [0, s1_val, s2_val, s3_val, s4_val, 4, 6]
        start_days = [1]  # Start day of first stay (Vienna) is 1
        for i in range(6):
            current_city = stay_city[i]
            start_days.append(start_days[i] + length_dict[current_city] - 1)
        
        itinerary = []
        for i in range(7):
            city = index_to_city[stay_city[i]]
            start = start_days[i]
            end = start + length_dict[stay_city[i]] - 1
            day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
            itinerary.append({"day_range": day_range, "place": city})
            
            if i < 6:
                next_city = index_to_city[stay_city[i+1]]
                itinerary.append({"day_range": f"Day {end}", "place": city})
                itinerary.append({"day_range": f"Day {end}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()