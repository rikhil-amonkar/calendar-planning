from z3 import *
import itertools

def main():
    # Define cities and days
    cities = ['Prague', 'Lyon', 'Frankfurt', 'Helsinki', 'Naples']
    days = list(range(1, 13))
    
    # Create solver and variables
    s = Solver()
    c_vars = {}
    for day in days:
        for city in cities:
            c_vars[(day, city)] = Bool(f"c_{day}_{city}")
    
    # Fixed constraints for the first 5 days
    # Day 1: Only in Prague
    s.add(c_vars[(1, 'Prague')] == True)
    for city in cities:
        if city != 'Prague':
            s.add(c_vars[(1, city)] == False)
    
    # Day 2: In Prague and Helsinki
    s.add(c_vars[(2, 'Prague')] == True)
    s.add(c_vars[(2, 'Helsinki')] == True)
    for city in ['Lyon', 'Frankfurt', 'Naples']:
        s.add(c_vars[(2, city)] == False)
    
    # Day 3: Only in Helsinki
    s.add(c_vars[(3, 'Helsinki')] == True)
    for city in ['Prague', 'Lyon', 'Frankfurt', 'Naples']:
        s.add(c_vars[(3, city)] == False)
    
    # Day 4: Only in Helsinki
    s.add(c_vars[(4, 'Helsinki')] == True)
    for city in ['Prague', 'Lyon', 'Frankfurt', 'Naples']:
        s.add(c_vars[(4, city)] == False)
    
    # Day 5: In Helsinki and either Naples or Frankfurt (exactly one)
    s.add(c_vars[(5, 'Helsinki')] == True)
    s.add(Or(c_vars[(5, 'Naples')], c_vars[(5, 'Frankfurt')]))
    s.add(Not(And(c_vars[(5, 'Naples')], c_vars[(5, 'Frankfurt')])))
    for city in ['Prague', 'Lyon']:
        s.add(c_vars[(5, city)] == False)
    
    # For days 6 to 12, not in Prague or Helsinki
    for day in range(6, 13):
        s.add(c_vars[(day, 'Prague')] == False)
        s.add(c_vars[(day, 'Helsinki')] == False)
    
    # Direct flight constraints
    edges_list = [
        ('Prague', 'Lyon'),
        ('Prague', 'Frankfurt'),
        ('Frankfurt', 'Lyon'),
        ('Helsinki', 'Naples'),
        ('Helsinki', 'Frankfurt'),
        ('Naples', 'Frankfurt'),
        ('Prague', 'Helsinki')
    ]
    edges_set = set()
    for a, b in edges_list:
        edges_set.add((a, b))
        edges_set.add((b, a))
    
    # For each day, ensure that if two cities are visited, they are connected by a direct flight
    for day in days:
        for i in range(len(cities)):
            for j in range(i + 1, len(cities)):
                city_i = cities[i]
                city_j = cities[j]
                if (city_i, city_j) not in edges_set:
                    s.add(Not(And(c_vars[(day, city_i)], c_vars[(day, city_j)])))
    
    # For each day, at most two cities can be visited
    for day in days:
        for triple in itertools.combinations(cities, 3):
            s.add(Not(And(
                c_vars[(day, triple[0])],
                c_vars[(day, triple[1])],
                c_vars[(day, triple[2])]
            )))
    
    # Each day must have at least one city
    for day in days:
        s.add(Or([c_vars[(day, city)] for city in cities]))
    
    # Total days per city constraints
    total_days = 0
    for city in cities:
        total = 0
        for day in days:
            total += If(c_vars[(day, city)], 1, 0)
        if city == 'Prague':
            s.add(total == 2)
        elif city == 'Lyon':
            s.add(total == 3)
        elif city == 'Frankfurt':
            s.add(total == 3)
        elif city == 'Helsinki':
            s.add(total == 4)
        elif city == 'Naples':
            s.add(total == 4)
        total_days += total
    
    # Total city-days must be 16
    s.add(total_days == 16)
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        schedule = {}
        for day in days:
            schedule[day] = []
            for city in cities:
                if m.evaluate(c_vars[(day, city)]):
                    schedule[day].append(city)
        
        # Print the schedule
        for day in sorted(schedule.keys()):
            cities_on_day = schedule[day]
            print(f"Day {day}: {', '.join(cities_on_day)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()