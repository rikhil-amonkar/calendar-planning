from z3 import *
import json

def main():
    cities = ['Reykjavik', 'Stuttgart', 'Istanbul', 'Vilnius', 'Seville', 'Geneva', 'Valencia', 'Munich']
    required_days = {
        'Reykjavik': 4,
        'Stuttgart': 4,
        'Istanbul': 4,
        'Vilnius': 4,
        'Seville': 3,
        'Geneva': 5,
        'Valencia': 5,
        'Munich': 3
    }

    directed_flights = set()
    
    bidirectional_pairs = [
        ('Geneva', 'Istanbul'),
        ('Reykjavik', 'Munich'),
        ('Stuttgart', 'Valencia'),
        ('Stuttgart', 'Istanbul'),
        ('Munich', 'Geneva'),
        ('Istanbul', 'Vilnius'),
        ('Valencia', 'Seville'),
        ('Valencia', 'Istanbul'),
        ('Seville', 'Munich'),
        ('Munich', 'Istanbul'),
        ('Valencia', 'Geneva'),
        ('Valencia', 'Munich')
    ]
    
    for (a, b) in bidirectional_pairs:
        directed_flights.add((a, b))
        directed_flights.add((b, a))
    
    unidirectional_pairs = [
        ('Reykjavik', 'Stuttgart'),
        ('Vilnius', 'Munich')
    ]
    for (a, b) in unidirectional_pairs:
        directed_flights.add((a, b))
    
    s = Solver()
    
    in_city = {}
    for city in cities:
        in_city[city] = [Bool(f'in_{city}_{day}') for day in range(1, 26)]
    
    for day in range(1, 26):
        or_expr = Or([in_city[city][day-1] for city in cities])
        s.add(or_expr)
        
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    c1 = cities[i]
                    c2 = cities[j]
                    c3 = cities[k]
                    s.add(Not(And(in_city[c1][day-1], in_city[c2][day-1], in_city[c3][day-1])))
    
    for city in cities:
        total_days = 0
        for day in range(1, 26):
            total_days += If(in_city[city][day-1], 1, 0)
        s.add(total_days == required_days[city])
    
    for day in [1, 2, 3, 4]:
        s.add(in_city['Reykjavik'][day-1])
    s.add(in_city['Stuttgart'][3]) 
    s.add(in_city['Stuttgart'][6])
    for day in [13, 14, 15]:
        s.add(in_city['Munich'][day-1])
    for day in [19, 20, 21, 22]:
        s.add(in_city['Istanbul'][day-1])
    
    for day in range(1, 26):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                in_both = And(in_city[c1][day-1], in_city[c2][day-1])
                flight_exists = Or(
                    (c1, c2) in directed_flights,
                    (c2, c1) in directed_flights
                )
                s.add(Implies(in_both, flight_exists))
    
    for day in range(1, 25):
        or_expr = []
        for city in cities:
            or_expr.append(And(in_city[city][day-1], in_city[city][day]))
        s.add(Or(or_expr))
    
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for day in range(1, 26):
            for city in cities:
                if is_true(m.evaluate(in_city[city][day-1])):
                    itinerary_list.append({"day": day, "place": city})
        itinerary_list.sort(key=lambda x: (x['day'], x['place']))
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()