from z3 import *

def main():
    cities = ["Oslo", "Stuttgart", "Venice", "Split", "Barcelona", "Brussels", "Copenhagen"]
    req = {
        "Oslo": 2,
        "Stuttgart": 3,
        "Venice": 4,
        "Split": 4,
        "Barcelona": 3,
        "Brussels": 3,
        "Copenhagen": 3
    }
    
    direct_flights_raw = [
        ("Venice", "Stuttgart"),
        ("Oslo", "Brussels"),
        ("Split", "Copenhagen"),
        ("Barcelona", "Copenhagen"),
        ("Barcelona", "Venice"),
        ("Brussels", "Venice"),
        ("Barcelona", "Stuttgart"),
        ("Copenhagen", "Brussels"),
        ("Oslo", "Split"),
        ("Oslo", "Venice"),
        ("Barcelona", "Split"),
        ("Oslo", "Copenhagen"),
        ("Barcelona", "Oslo"),
        ("Copenhagen", "Stuttgart"),
        ("Split", "Stuttgart"),
        ("Copenhagen", "Venice"),
        ("Barcelona", "Brussels")
    ]
    
    flight_set = set()
    for a, b in direct_flights_raw:
        if a < b:
            flight_set.add((a, b))
        else:
            flight_set.add((b, a))
    
    in_city = {}
    for city in cities:
        in_city[city] = [Bool(f"in_{city}_{d}") for d in range(16)]
    
    s = Solver()
    
    for d in range(16):
        day_bools = [in_city[city][d] for city in cities]
        s.add(Sum([If(b, 1, 0) for b in day_bools]) >= 1)
        s.add(Sum([If(b, 1, 0) for b in day_bools]) <= 2)
    
    for city in cities:
        total_days = Sum([If(in_city[city][d], 1, 0) for d in range(16)])
        s.add(total_days == req[city])
    
    s.add(in_city["Barcelona"][0] == True)
    s.add(in_city["Barcelona"][1] == True)
    s.add(in_city["Barcelona"][2] == True)
    
    s.add(Or(in_city["Oslo"][2], in_city["Oslo"][3]))
    
    s.add(Or(in_city["Brussels"][8], in_city["Brussels"][9], in_city["Brussels"][10]))
    
    for d in range(15):
        common_city = Or([And(in_city[city][d], in_city[city][d+1]) for city in cities])
        s.add(common_city)
    
    for d in range(16):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                pair = (c1, c2) if c1 < c2 else (c2, c1)
                if pair not in flight_set:
                    s.add(Not(And(in_city[c1][d], in_city[c2][d])))
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for d in range(16):
            day_cities = []
            for city in cities:
                if m.evaluate(in_city[city][d]):
                    day_cities.append(city)
            schedule.append(day_cities)
        
        for d in range(16):
            print(f"Day {d+1}: {', '.join(schedule[d])}")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()