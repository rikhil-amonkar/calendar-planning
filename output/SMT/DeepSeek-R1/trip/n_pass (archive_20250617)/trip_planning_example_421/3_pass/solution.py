from z3 import *

def main():
    cities = ['Nice', 'Krakow', 'Dublin', 'Lyon', 'Frankfurt']
    days = list(range(1, 21))
    
    s = Solver()
    
    in_city = {}
    for c in cities:
        for d in days:
            in_city[(c, d)] = Bool(f'in_{c}_{d}')
    
    s.add(Sum([If(in_city[('Nice', d)], 1, 0) for d in days]) == 5)
    s.add(Sum([If(in_city[('Krakow', d)], 1, 0) for d in days]) == 6)
    s.add(Sum([If(in_city[('Dublin', d)], 1, 0) for d in days]) == 7)
    s.add(Sum([If(in_city[('Lyon', d)], 1, 0) for d in days]) == 4)
    s.add(Sum([If(in_city[('Frankfurt', d)], 1, 0) for d in days]) == 2)
    
    for d in range(6, 21):
        s.add(in_city[('Nice', d)] == False)
    
    s.add(in_city[('Frankfurt', 19)] == True)
    s.add(in_city[('Frankfurt', 20)] == True)
    for d in range(1, 19):
        s.add(in_city[('Frankfurt', d)] == False)
    
    for d in days:
        s.add(Or(
            Sum([If(in_city[(c, d)], 1, 0) for c in cities]) == 1,
            Sum([If(in_city[(c, d)], 1, 0) for c in cities]) == 2
        ))
    
    for d in range(1, 20):
        s.add(Or([And(in_city[(c, d)], in_city[(c, d+1)]) for c in cities]))
    
    allowed_pairs = [
        ('Nice', 'Dublin'),
        ('Dublin', 'Frankfurt'),
        ('Dublin', 'Krakow'),
        ('Krakow', 'Frankfurt'),
        ('Lyon', 'Frankfurt'),
        ('Nice', 'Frankfurt'),
        ('Lyon', 'Dublin'),
        ('Nice', 'Lyon')
    ]
    
    for d in days:
        total_cities = Sum([If(in_city[(c, d)], 1, 0) for c in cities])
        or_list = []
        for (c1, c2) in allowed_pairs:
            or_list.append(And(in_city[(c1, d)], in_city[(c2, d)]))
        s.add(Implies(total_cities == 2, Or(or_list)))
    
    # Ensure Frankfurt is alone on day 20
    for c in cities:
        if c != 'Frankfurt':
            s.add(in_city[(c, 20)] == False)
    
    if s.check() == sat:
        model = s.model()
        for d in days:
            cities_today = [c for c in cities if model.evaluate(in_city[(c, d)])]
            print(f"Day {d}: {', '.join(cities_today)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()