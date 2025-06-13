from z3 import *

def main():
    cities = ['Valencia', 'Oslo', 'Lyon', 'Prague', 'Paris', 'Nice', 'Seville', 'Tallinn', 'Mykonos', 'Lisbon']
    
    total_days = {
        'Valencia': 2,
        'Oslo': 3,
        'Lyon': 4,
        'Prague': 3,
        'Paris': 4,
        'Nice': 4,
        'Seville': 5,
        'Tallinn': 2,
        'Mykonos': 5,
        'Lisbon': 2
    }
    
    flight_strings = [
        "Lisbon and Paris", "Lyon and Nice", "Tallinn and Oslo", "Prague and Lyon", "Paris and Oslo", 
        "Lisbon and Seville", "Prague and Lisbon", "Oslo and Nice", "Valencia and Paris", 
        "Valencia and Lisbon", "Paris and Nice", "Nice and Mykonos", "Paris and Lyon", 
        "Valencia and Lyon", "Prague and Oslo", "Prague and Paris", "Seville and Paris", 
        "Oslo and Lyon", "Prague and Valencia", "Lisbon and Nice", "Lisbon and Oslo", 
        "Valencia and Seville", "Lisbon and Lyon", "Paris and Tallinn", "Prague and Tallinn"
    ]
    
    flight_set = set()
    for s in flight_strings:
        c1, c2 = s.split(" and ")
        if c1 < c2:
            flight_set.add((c1, c2))
        else:
            flight_set.add((c2, c1))
    
    s = Solver()
    
    present = {}
    for city in cities:
        present[city] = { day: Bool(f"{city}_{day}") for day in range(1, 26) }
    
    for day in [5, 6, 7, 8, 9]:
        s.add(present['Seville'][day] == True)
    for day in [21, 22, 23, 24, 25]:
        s.add(present['Mykonos'][day] == True)
    
    s.add(Or(present['Valencia'][3], present['Valencia'][4]))
    s.add(Or(present['Oslo'][13], present['Oslo'][14], present['Oslo'][15]))
    
    for city in cities:
        s.add(Sum([If(present[city][day], 1, 0) for day in range(1, 26)]) == total_days[city])
    
    for day in range(1, 26):
        day_vars = [present[city][day] for city in cities]
        s.add(Sum([If(var, 1, 0) for var in day_vars]) >= 1)
        s.add(Sum([If(var, 1, 0) for var in day_vars]) <= 2)
    
    for day in [5, 6, 7, 8, 9]:
        for city in cities:
            if city == 'Seville':
                continue
            c1, c2 = sorted(['Seville', city])
            if (c1, c2) not in flight_set:
                s.add(present[city][day] == False)
    
    for day in [21, 22, 23, 24, 25]:
        for city in cities:
            if city == 'Mykonos':
                continue
            c1, c2 = sorted(['Mykonos', city])
            if (c1, c2) not in flight_set:
                s.add(present[city][day] == False)
    
    for day in range(1, 26):
        for i in range(len(cities)):
            for j in range(i + 1, len(cities)):
                A = cities[i]
                B = cities[j]
                c1, c2 = sorted([A, B])
                if (c1, c2) not in flight_set:
                    s.add(Not(And(present[A][day], present[B][day])))
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for day in range(1, 26):
            cities_today = []
            for city in cities:
                if m.evaluate(present[city][day]):
                    cities_today.append(city)
            schedule.append((day, cities_today))
        for day, cities_list in schedule:
            print(f"Day {day}: {cities_list}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()