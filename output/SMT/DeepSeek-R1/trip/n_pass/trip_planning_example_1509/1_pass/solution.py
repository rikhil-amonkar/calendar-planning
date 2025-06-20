from z3 import *

def main():
    City = Datatype('City')
    for c in ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']:
        City.declare(c)
    City = City.create()
    
    cities = [getattr(City, c) for c in ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']]
    city_names = {c: c_name for c_name in ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon'] for c in [getattr(City, c_name)]}
    
    allowed_pairs = []
    bidirectional = [
        ("Warsaw", "Riga"),
        ("Warsaw", "Tallinn"),
        ("Copenhagen", "Helsinki"),
        ("Lyon", "Paris"),
        ("Copenhagen", "Warsaw"),
        ("Lyon", "Oslo"),
        ("Paris", "Oslo"),
        ("Paris", "Riga"),
        ("Krakow", "Helsinki"),
        ("Paris", "Tallinn"),
        ("Oslo", "Riga"),
        ("Krakow", "Warsaw"),
        ("Paris", "Helsinki"),
        ("Copenhagen", "Santorini"),
        ("Helsinki", "Warsaw"),
        ("Helsinki", "Riga"),
        ("Copenhagen", "Krakow"),
        ("Copenhagen", "Riga"),
        ("Paris", "Krakow"),
        ("Copenhagen", "Oslo"),
        ("Oslo", "Tallinn"),
        ("Oslo", "Helsinki"),
        ("Copenhagen", "Tallinn"),
        ("Oslo", "Krakow"),
        ("Helsinki", "Tallinn"),
        ("Paris", "Copenhagen"),
        ("Paris", "Warsaw"),
        ("Oslo", "Warsaw")
    ]
    unidirectional = [
        ("Riga", "Tallinn"),
        ("Santorini", "Oslo")
    ]
    
    for (a, b) in bidirectional:
        c1 = getattr(City, a)
        c2 = getattr(City, b)
        allowed_pairs.append((c1, c2))
        allowed_pairs.append((c2, c1))
    for (a, b) in unidirectional:
        c1 = getattr(City, a)
        c2 = getattr(City, b)
        allowed_pairs.append((c1, c2))
    
    base_city = [None]
    for d in range(1, 26):
        base_city.append(Const(f'base_city_{d}', City))
    
    flight = [None]
    next_city = [None]
    for d in range(1, 25):
        flight.append(Bool(f'flight_{d}'))
        next_city.append(Const(f'next_city_{d}', City))
    
    s = Solver()
    
    for d in [4,5,6,7,8]:
        s.add(base_city[d] == City.Paris)
    s.add(base_city[13] == City.Santorini)
    s.add(base_city[18] == City.Krakow)
    s.add(base_city[24] == City.Riga)
    
    for d in [4,5,6,7]:
        s.add(flight[d] == False)
    
    for d in range(1, 25):
        s.add(base_city[d+1] == If(flight[d], next_city[d], base_city[d]))
    
    total_flights = 0
    for d in range(1, 25):
        if d not in [4,5,6,7]:
            total_flights += If(flight[d], 1, 0)
    s.add(total_flights == 9)
    
    for d in range(1, 25):
        if d in [4,5,6,7]:
            continue
        s.add(Implies(flight[d], base_city[d] != next_city[d]))
        conds = []
        for (c1, c2) in allowed_pairs:
            conds.append(And(base_city[d] == c1, next_city[d] == c2))
        s.add(Implies(flight[d], Or(conds)))
    
    counts = {c: 0 for c in cities}
    for c in cities:
        for d in range(1, 26):
            counts[c] += If(base_city[d] == c, 1, 0)
        for d in range(1, 25):
            counts[c] += If(And(flight[d], next_city[d] == c), 1, 0)
    
    s.add(counts[City.Paris] == 5)
    s.add(counts[City.Warsaw] == 2)
    s.add(counts[City.Krakow] == 2)
    s.add(counts[City.Tallinn] == 2)
    s.add(counts[City.Riga] == 2)
    s.add(counts[City.Copenhagen] == 5)
    s.add(counts[City.Helsinki] == 5)
    s.add(counts[City.Oslo] == 5)
    s.add(counts[City.Santorini] == 2)
    s.add(counts[City.Lyon] == 4)
    
    helsinki_constraint = []
    for d in [18,19,20,21,22]:
        helsinki_constraint.append(Or(base_city[d] == City.Helsinki, And(flight[d], next_city[d] == City.Helsinki)))
    s.add(Or(helsinki_constraint))
    
    if s.check() == sat:
        m = s.model()
        base_city_vals = [m.eval(base_city[d]) for d in range(1,26)]
        flight_vals = [m.eval(flight[d]) for d in range(1,25)]
        next_city_vals = [m.eval(next_city[d]) for d in range(1,25)]
        
        base_city_names = [city_names[base_city_vals[d-1]] for d in range(1,26)]
        next_city_names = [city_names[next_city_vals[d-1]] if d < 25 else None for d in range(1,25)]
        flight_vals_bool = [is_true(flight_vals[d-1]) for d in range(1,25)]
        
        itinerary = []
        start = 1
        current_city = base_city_names[0]
        for d in range(1, 25):
            if flight_vals_bool[d-1]:
                if start <= d:
                    if start == d:
                        day_str = f"Day {d}"
                    else:
                        day_str = f"Day {start}-{d}"
                    itinerary.append({"day_range": day_str, "place": current_city})
                itinerary.append({"day_range": f"Day {d}", "place": current_city})
                next_c = next_city_names[d-1]
                itinerary.append({"day_range": f"Day {d}", "place": next_c})
                current_city = next_c
                start = d
            else:
                pass
        if start <= 25:
            if start == 25:
                day_str = "Day 25"
            else:
                day_str = f"Day {start}-25"
            itinerary.append({"day_range": day_str, "place": current_city})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()