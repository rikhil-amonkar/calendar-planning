from z3 import *

def main():
    days = list(range(1, 23))
    cities = ['Brussels', 'Helsinki', 'Split', 'Dubrovnik', 'Istanbul', 'Milan', 'Vilnius', 'Frankfurt']
    
    in_city = {}
    for d in days:
        for c in cities:
            in_city[(d, c)] = Bool(f"in_{d}_{c}")
    
    s = Solver()
    
    # Fixed constraints for Istanbul: days 1-5 inclusive
    for d in range(1, 6):
        s.add(in_city[(d, 'Istanbul')])
    for d in range(6, 23):
        s.add(Not(in_city[(d, 'Istanbul')]))
    
    # Fixed constraints for Vilnius: days 18-22 inclusive
    for d in range(1, 18):
        s.add(Not(in_city[(d, 'Vilnius')]))
    for d in range(18, 23):
        s.add(in_city[(d, 'Vilnius')])
    
    # Fixed constraints for Frankfurt: days 16-18 inclusive
    for d in range(1, 16):
        s.add(Not(in_city[(d, 'Frankfurt')]))
    for d in range(16, 19):
        s.add(in_city[(d, 'Frankfurt')])
    for d in range(19, 23):
        s.add(Not(in_city[(d, 'Frankfurt')]))
    
    # Total days for other cities
    total_days = {
        'Brussels': 3,
        'Helsinki': 3,
        'Split': 4,
        'Dubrovnik': 2,
        'Milan': 4
    }
    for city, total in total_days.items():
        s.add(Sum([If(in_city[(d, city)], 1, 0) for d in days]) == total)
    
    # Define allowed flight pairs (as frozenset for unordered pairs)
    bidirectional_connections = [
        ('Milan', 'Frankfurt'),
        ('Split', 'Frankfurt'),
        ('Milan', 'Split'),
        ('Brussels', 'Vilnius'),
        ('Brussels', 'Helsinki'),
        ('Istanbul', 'Brussels'),
        ('Milan', 'Vilnius'),
        ('Brussels', 'Milan'),
        ('Istanbul', 'Helsinki'),
        ('Helsinki', 'Vilnius'),
        ('Helsinki', 'Dubrovnik'),
        ('Split', 'Vilnius'),
        ('Istanbul', 'Milan'),
        ('Helsinki', 'Frankfurt'),
        ('Istanbul', 'Vilnius'),
        ('Split', 'Helsinki'),
        ('Milan', 'Helsinki'),
        ('Istanbul', 'Frankfurt'),
        ('Dubrovnik', 'Frankfurt'),
        ('Frankfurt', 'Vilnius')
    ]
    unidirectional_connections = [
        ('Dubrovnik', 'Istanbul'),
        ('Brussels', 'Frankfurt')
    ]
    allowed_pairs = set()
    for a, b in bidirectional_connections:
        allowed_pairs.add(frozenset({a, b}))
    for a, b in unidirectional_connections:
        allowed_pairs.add(frozenset({a, b}))
    
    # Constraints for each day: at least one city, at most two cities, and allowed pairs if two cities
    for d in days:
        bools = [in_city[(d, c)] for c in cities]
        s.add(Or(bools))  # At least one city per day
        s.add(AtMost(*bools, 2))  # At most two cities per day
        
        for i in range(len(cities)):
            for j in range(i + 1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                pair = frozenset({c1, c2})
                if pair not in allowed_pairs:
                    s.add(Or(Not(in_city[(d, c1)]), Not(in_city[(d, c2)])))
    
    # Continuity constraint: consecutive days must share at least one city
    for d in range(1, 22):
        common_cities = [And(in_city[(d, c)], in_city[(d + 1, c)]) for c in cities]
        s.add(Or(common_cities))
    
    # Solve and output the plan
    if s.check() == sat:
        m = s.model()
        plan = []
        for d in days:
            cities_today = [c for c in cities if m.evaluate(in_city[(d, c)]).eq(True)]
            plan.append((d, cities_today))
        for d, cities_list in plan:
            print(f"Day {d}: {cities_list}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()