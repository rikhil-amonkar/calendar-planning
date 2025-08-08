from z3 import *
import json

def main():
    # Total days
    days = list(range(1, 22))  # Days 1 to 21
    cities = ['Manchester', 'Istanbul', 'Venice', 'Krakow', 'Lyon']
    
    required_days = {
        'Manchester': 3,
        'Istanbul': 7,
        'Venice': 7,
        'Krakow': 6,
        'Lyon': 2
    }
    
    flight_edges = [
        ('Manchester', 'Venice'),
        ('Manchester', 'Istanbul'),
        ('Venice', 'Istanbul'),
        ('Istanbul', 'Krakow'),
        ('Venice', 'Lyon'),
        ('Lyon', 'Istanbul'),
        ('Manchester', 'Krakow')
    ]
    
    flight_set = set()
    for edge in flight_edges:
        flight_set.add(frozenset(edge))
    
    s = Solver()
    
    in_city = {}
    for city in cities:
        in_city[city] = {}
        for day in days:
            in_city[city][day] = Bool(f"in_{city}_{day}")
    
    # Constraint 1: Each day has 1 or 2 cities
    for day in days:
        bool_list = [in_city[city][day] for city in cities]
        s.add(Or(PbEq([(x, 1) for x in bool_list], 1), PbEq([(x, 1) for x in bool_list], 2)))
    
    # Constraint 2: If two cities on the same day, they must be connected by a direct flight
    for day in days:
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                if frozenset([c1, c2]) not in flight_set:
                    s.add(Not(And(in_city[c1][day], in_city[c2][day])))
    
    # Constraint 3: Total days per city
    for city in cities:
        total = 0
        for day in days:
            total += If(in_city[city][day], 1, 0)
        s.add(total == required_days[city])
    
    # Constraint 4: Event constraints
    manchester_days = Or(in_city['Manchester'][1], in_city['Manchester'][2], in_city['Manchester'][3])
    s.add(manchester_days)
    
    venice_days = [in_city['Venice'][d] for d in range(3, 10)]
    s.add(Or(venice_days))
    
    # Constraint 5: Continuity between consecutive days
    for d in range(1, 21):
        common_city = Or([And(in_city[city][d], in_city[city][d+1]) for city in cities])
        s.add(common_city)
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for day in days:
            for city in cities:
                if m.evaluate(in_city[city][day]):
                    itinerary_list.append({"day": day, "place": city})
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == '__main__':
    main()