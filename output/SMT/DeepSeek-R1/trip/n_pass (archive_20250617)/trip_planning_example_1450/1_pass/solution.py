from z3 import *

def main():
    s = Solver()
    
    cities = ['Stockholm', 'Hamburg', 'Florence', 'Istanbul', 'Oslo', 'Vilnius', 'Santorini', 'Munich', 'Frankfurt', 'Krakow']
    n_cities = len(cities)
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    
    flights = [
        ("Oslo", "Stockholm"), ("Stockholm", "Oslo"),
        ("Krakow", "Frankfurt"), ("Frankfurt", "Krakow"),
        ("Krakow", "Istanbul"), ("Istanbul", "Krakow"),
        ("Munich", "Stockholm"), ("Stockholm", "Munich"),
        ("Hamburg", "Stockholm"), ("Stockholm", "Hamburg"),
        ("Krakow", "Vilnius"),
        ("Oslo", "Istanbul"), ("Istanbul", "Oslo"),
        ("Istanbul", "Stockholm"), ("Stockholm", "Istanbul"),
        ("Oslo", "Krakow"), ("Krakow", "Oslo"),
        ("Vilnius", "Istanbul"), ("Istanbul", "Vilnius"),
        ("Oslo", "Vilnius"), ("Vilnius", "Oslo"),
        ("Frankfurt", "Istanbul"), ("Istanbul", "Frankfurt"),
        ("Oslo", "Frankfurt"), ("Frankfurt", "Oslo"),
        ("Munich", "Hamburg"), ("Hamburg", "Munich"),
        ("Florence", "Munich"),
        ("Krakow", "Munich"), ("Munich", "Krakow"),
        ("Hamburg", "Istanbul"), ("Istanbul", "Hamburg"),
        ("Frankfurt", "Stockholm"), ("Stockholm", "Frankfurt"),
        ("Stockholm", "Santorini"),
        ("Frankfurt", "Munich"), ("Munich", "Frankfurt"),
        ("Santorini", "Oslo"),
        ("Krakow", "Stockholm"), ("Stockholm", "Krakow"),
        ("Vilnius", "Munich")
    ]
    flight_set = set()
    for f in flights:
        from_city, to_city = f
        idx1 = city_to_int[from_city]
        idx2 = city_to_int[to_city]
        flight_set.add((idx1, idx2))
    
    req_days = {
        'Stockholm': 3,
        'Hamburg': 5,
        'Florence': 2,
        'Istanbul': 5,
        'Oslo': 5,
        'Vilnius': 5,
        'Santorini': 2,
        'Munich': 5,
        'Frankfurt': 4,
        'Krakow': 5
    }
    
    city_start = [Int('city_start_%d' % i) for i in range(1, 33)]
    travel = [Bool('travel_%d' % i) for i in range(1, 32)]
    
    for i in range(32):
        s.add(city_start[i] >= 0, city_start[i] < n_cities)
    
    for i in range(31):
        s.add(Implies(Not(travel[i]), city_start[i] == city_start[i+1]))
        s.add(Implies(travel[i], Or([And(city_start[i] == f[0], city_start[i+1] == f[1]) for f in flight_set])))
    
    istanbul_idx = city_to_int['Istanbul']
    for d in [24, 25, 26, 27, 28]:
        s.add(Or(city_start[d] == istanbul_idx, And(travel[d], city_start[d+1] == istanbul_idx)))
    
    krakow_idx = city_to_int['Krakow']
    for d in [4, 5, 6, 7, 8]:
        s.add(Or(city_start[d] == krakow_idx, And(travel[d], city_start[d+1] == krakow_idx)))
    
    for cidx, city in enumerate(cities):
        total_req = req_days[city]
        count1 = Sum([If(city_start[i] == cidx, 1, 0) for i in range(32)])
        count2 = Sum([If(And(travel[i], city_start[i+1] == cidx, city_start[i] != cidx), 1, 0) for i in range(31)])
        s.add(count1 + count2 == total_req)
    
    if s.check() == sat:
        m = s.model()
        plan = []
        for i in range(32):
            cidx = m[city_start[i]].as_long()
            plan.append(cities[cidx])
        travel_flags = []
        for i in range(31):
            travel_flags.append(m[travel[i]])
        
        print("Day\tCity")
        for i in range(32):
            if i < 31 and travel_flags[i]:
                print(f"{i+1}\t{plan[i]} and {plan[i+1]} (travel day)")
            else:
                print(f"{i+1}\t{plan[i]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()