from z3 import *

def main():
    cities = ['Prague', 'Lyon', 'Frankfurt', 'Helsinki', 'Naples']
    days = list(range(1, 13))
    
    direct_flights = [
        ('Prague', 'Lyon'),
        ('Prague', 'Frankfurt'),
        ('Frankfurt', 'Lyon'),
        ('Helsinki', 'Naples'),
        ('Helsinki', 'Frankfurt'),
        ('Naples', 'Frankfurt'),
        ('Prague', 'Helsinki')
    ]
    allowed = set()
    for a, b in direct_flights:
        allowed.add((a, b))
        allowed.add((b, a))
    
    s = Solver()
    c_vars = {}
    for day in days:
        for city in cities:
            c_vars[(day, city)] = Bool(f"c_{day}_{city}")
    
    fixed_schedule = {
        1: ['Prague'],
        2: ['Prague', 'Helsinki'],
        3: ['Helsinki'],
        4: ['Helsinki'],
        5: ['Helsinki', 'Naples'],
        6: ['Naples'],
        7: ['Naples'],
        8: ['Naples', 'Frankfurt'],
        9: ['Frankfurt'],
        10: ['Frankfurt', 'Lyon'],
        11: ['Lyon'],
        12: ['Lyon']
    }
    
    for day, city_list in fixed_schedule.items():
        for city in cities:
            if city in city_list:
                s.add(c_vars[(day, city)] == True)
            else:
                s.add(c_vars[(day, city)] == False)
    
    for day in days:
        for i in range(len(cities)):
            for j in range(i + 1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                if (c1, c2) not in allowed:
                    s.add(Not(And(c_vars[(day, c1)], c_vars[(day, c2)])))
    
    for d in range(1, 12):
        s.add(Or([And(c_vars[(d, city)], c_vars[(d+1, city)]) for city in cities]))
    
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
    s.add(total_days == 16)
    
    if s.check() == sat:
        m = s.model()
        schedule = {}
        for day in days:
            schedule[day] = []
            for city in cities:
                if m.evaluate(c_vars[(day, city)]):
                    schedule[day].append(city)
        for day in sorted(schedule.keys()):
            print(f"Day {day}: {', '.join(schedule[day])}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()