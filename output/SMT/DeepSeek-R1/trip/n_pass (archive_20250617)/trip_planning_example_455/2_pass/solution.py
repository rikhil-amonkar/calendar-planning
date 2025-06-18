from z3 import Solver, Bool, Sum, If, And, Or, Not, sat

def main():
    cities = ['Reykjavik', 'Riga', 'Warsaw', 'Istanbul', 'Krakow']
    required_days = {
        'Reykjavik': 7,
        'Riga': 2,
        'Warsaw': 3,
        'Istanbul': 6,
        'Krakow': 7
    }
    total_days = 21

    flights_list = [
        ('Istanbul', 'Krakow'),
        ('Warsaw', 'Reykjavik'),
        ('Istanbul', 'Warsaw'),
        ('Riga', 'Istanbul'),
        ('Krakow', 'Warsaw'),
        ('Riga', 'Warsaw')
    ]
    
    flight_set = set()
    for a, b in flights_list:
        key = tuple(sorted([a, b]))
        flight_set.add(key)
    
    non_flight_pairs = []
    for i in range(len(cities)):
        for j in range(i+1, len(cities)):
            c1 = cities[i]
            c2 = cities[j]
            key = tuple(sorted([c1, c2]))
            if key not in flight_set:
                non_flight_pairs.append((c1, c2))
    
    s = Solver()
    in_city = {}
    for day in range(1, total_days + 1):
        for city in cities:
            in_city[(day, city)] = Bool(f"in_{day}_{city}")
    
    for day in range(1, total_days + 1):
        cities_day = [in_city[(day, c)] for c in cities]
        s.add(Sum([If(var, 1, 0) for var in cities_day]) >= 1)
        s.add(Sum([If(var, 1, 0) for var in cities_day]) <= 2)
    
    for day in range(1, total_days + 1):
        for (c1, c2) in non_flight_pairs:
            s.add(Not(And(in_city[(day, c1)], in_city[(day, c2)])))
    
    for day in range(1, total_days):
        common_city = [And(in_city[(day, c)], in_city[(day+1, c)]) for c in cities]
        s.add(Or(common_city))
    
    s.add(Or(in_city[(1, 'Riga')], in_city[(2, 'Riga')]))
    s.add(Or([in_city[(d, 'Istanbul')] for d in range(2, 8)]))
    
    for city in cities:
        total = Sum([If(in_city[(d, city)], 1, 0) for d in range(1, total_days+1)])
        s.add(total == required_days[city])
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for day in range(1, total_days + 1):
            cities_today = []
            for city in cities:
                if m.evaluate(in_city[(day, city)]):
                    cities_today.append(city)
            schedule.append((day, cities_today))
        
        for day, cities_list in schedule:
            print(f"Day {day}: {', '.join(cities_list)}")
    else:
        print("No valid schedule found.")

if __name__ == "__main__":
    main()