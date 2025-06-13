from z3 import *

def main():
    cities = ["Warsaw", "Porto", "Naples", "Brussels", "Split", "Reykjavik", "Amsterdam", "Lyon", "Helsinki", "Valencia"]
    n_cities = len(cities)
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    flights_str = [
        "Amsterdam and Warsaw", 
        "Helsinki and Brussels", 
        "Helsinki and Warsaw", 
        "Reykjavik and Brussels", 
        "Amsterdam and Lyon", 
        "Amsterdam and Naples", 
        "Amsterdam and Reykjavik", 
        "Naples and Valencia", 
        "Porto and Brussels", 
        "Amsterdam and Split", 
        "Lyon and Split", 
        "Warsaw and Split", 
        "Porto and Amsterdam", 
        "Helsinki and Split", 
        "Brussels and Lyon", 
        "Porto and Lyon", 
        "Reykjavik and Warsaw", 
        "Brussels and Valencia", 
        "Valencia and Lyon", 
        "Porto and Warsaw", 
        "Warsaw and Valencia", 
        "Amsterdam and Helsinki", 
        "Porto and Valencia", 
        "Warsaw and Brussels", 
        "Warsaw and Naples", 
        "Naples and Split", 
        "Helsinki and Naples", 
        "Helsinki and Reykjavik", 
        "Amsterdam and Valencia", 
        "Naples and Brussels"
    ]
    
    direct_flights = set()
    for s in flights_str:
        parts = s.split(" and ")
        c1, c2 = parts[0], parts[1]
        idx1 = city_index[c1]
        idx2 = city_index[c2]
        direct_flights.add((min(idx1, idx2), max(idx1, idx2)))
    
    base_city = [Int(f'base_city_{i}') for i in range(28)]
    flight = [Bool(f'flight_{i}') for i in range(1, 28)]
    
    s = Solver()
    
    for i in range(28):
        s.add(base_city[i] >= 0, base_city[i] < n_cities)
    
    for i in range(1, 28):
        s.add(Implies(Not(flight[i-1]), base_city[i] == base_city[i-1]))
    
    for i in range(1, 28):
        a, b = base_city[i-1], base_city[i]
        min_ab = If(a < b, a, b)
        max_ab = If(a < b, b, a)
        flight_exists = Or([And(min_ab == p[0], max_ab == p[1]) for p in direct_flights])
        s.add(Implies(flight[i-1], And(a != b, flight_exists)))
    
    s.add(Sum([If(f, 1, 0) for f in flight]) == 9)
    
    total_days_req = [3, 5, 4, 3, 3, 5, 4, 3, 4, 2]
    for c in range(n_cities):
        total = 0
        for i in range(1, 28):
            if i == 1:
                total += If(flight[0], 
                            If(base_city[0] == c, 1, 0) + If(base_city[1] == c, 1, 0),
                            If(base_city[0] == c, 1, 0))
            else:
                total += If(flight[i-1],
                            If(base_city[i-1] == c, 1, 0) + If(base_city[i] == c, 1, 0),
                            If(base_city[i-1] == c, 1, 0))
        s.add(total == total_days_req[c])
    
    naples_idx = city_index["Naples"]
    s.add(Or(
        And(flight[16], Or(base_city[16] == naples_idx, base_city[17] == naples_idx)),
        And(Not(flight[16]), base_city[16] == naples_idx)
    ))
    s.add(Or(
        And(flight[17], Or(base_city[17] == naples_idx, base_city[18] == naples_idx)),
        And(Not(flight[17]), base_city[17] == naples_idx)
    ))
    s.add(Or(
        And(flight[18], Or(base_city[18] == naples_idx, base_city[19] == naples_idx)),
        And(Not(flight[18]), base_city[18] == naples_idx)
    ))
    s.add(Or(
        And(flight[19], Or(base_city[19] == naples_idx, base_city[20] == naples_idx)),
        And(Not(flight[19]), base_city[19] == naples_idx)
    ))
    
    brussels_idx = city_index["Brussels"]
    s.add(Or(
        And(flight[19], Or(base_city[19] == brussels_idx, base_city[20] == brussels_idx)),
        And(Not(flight[19]), base_city[19] == brussels_idx)
    ))
    s.add(Or(
        And(flight[20], Or(base_city[20] == brussels_idx, base_city[21] == brussels_idx)),
        And(Not(flight[20]), base_city[20] == brussels_idx)
    ))
    s.add(Or(
        And(flight[21], Or(base_city[21] == brussels_idx, base_city[22] == brussels_idx)),
        And(Not(flight[21]), base_city[21] == brussels_idx)
    ))
    
    porto_idx = city_index["Porto"]
    porto_conds = []
    porto_conds.append(Or(
        And(flight[0], Or(base_city[0] == porto_idx, base_city[1] == porto_idx)),
        And(Not(flight[0]), base_city[0] == porto_idx)
    ))
    porto_conds.append(Or(
        And(flight[1], Or(base_city[1] == porto_idx, base_city[2] == porto_idx)),
        And(Not(flight[1]), base_city[1] == porto_idx)
    ))
    porto_conds.append(Or(
        And(flight[2], Or(base_city[2] == porto_idx, base_city[3] == porto_idx)),
        And(Not(flight[2]), base_city[2] == porto_idx)
    ))
    porto_conds.append(Or(
        And(flight[3], Or(base_city[3] == porto_idx, base_city[4] == porto_idx)),
        And(Not(flight[3]), base_city[3] == porto_idx)
    ))
    porto_conds.append(Or(
        And(flight[4], Or(base_city[4] == porto_idx, base_city[5] == porto_idx)),
        And(Not(flight[4]), base_city[4] == porto_idx)
    ))
    s.add(Or(porto_conds))
    
    amsterdam_idx = city_index["Amsterdam"]
    amsterdam_conds = []
    amsterdam_conds.append(Or(
        And(flight[4], Or(base_city[4] == amsterdam_idx, base_city[5] == amsterdam_idx)),
        And(Not(flight[4]), base_city[4] == amsterdam_idx)
    ))
    amsterdam_conds.append(Or(
        And(flight[5], Or(base_city[5] == amsterdam_idx, base_city[6] == amsterdam_idx)),
        And(Not(flight[5]), base_city[5] == amsterdam_idx)
    ))
    amsterdam_conds.append(Or(
        And(flight[6], Or(base_city[6] == amsterdam_idx, base_city[7] == amsterdam_idx)),
        And(Not(flight[6]), base_city[6] == amsterdam_idx)
    ))
    amsterdam_conds.append(Or(
        And(flight[7], Or(base_city[7] == amsterdam_idx, base_city[8] == amsterdam_idx)),
        And(Not(flight[7]), base_city[7] == amsterdam_idx)
    ))
    s.add(Or(amsterdam_conds))
    
    helsinki_idx = city_index["Helsinki"]
    helsinki_conds = []
    helsinki_conds.append(Or(
        And(flight[7], Or(base_city[7] == helsinki_idx, base_city[8] == helsinki_idx)),
        And(Not(flight[7]), base_city[7] == helsinki_idx)
    ))
    helsinki_conds.append(Or(
        And(flight[8], Or(base_city[8] == helsinki_idx, base_city[9] == helsinki_idx)),
        And(Not(flight[8]), base_city[8] == helsinki_idx)
    ))
    helsinki_conds.append(Or(
        And(flight[9], Or(base_city[9] == helsinki_idx, base_city[10] == helsinki_idx)),
        And(Not(flight[9]), base_city[9] == helsinki_idx)
    ))
    helsinki_conds.append(Or(
        And(flight[10], Or(base_city[10] == helsinki_idx, base_city[11] == helsinki_idx)),
        And(Not(flight[10]), base_city[10] == helsinki_idx)
    ))
    s.add(Or(helsinki_conds))
    
    if s.check() == sat:
        m = s.model()
        result = []
        for i in range(1, 28):
            f_val = m.evaluate(flight[i-1])
            if f_val:
                from_city = m.evaluate(base_city[i-1])
                to_city = m.evaluate(base_city[i])
                from_city_name = cities[from_city.as_long()]
                to_city_name = cities[to_city.as_long()]
                result.append(f"Day {i}: Fly from {from_city_name} to {to_city_name}")
            else:
                c = m.evaluate(base_city[i-1])
                c_name = cities[c.as_long()]
                result.append(f"Day {i}: Stay in {c_name}")
        for line in result:
            print(line)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()