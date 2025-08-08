from z3 import *
import json

def main():
    cities = ['Brussels', 'Venice', 'London', 'Lisbon', 'Reykjavik', 'Santorini', 'Madrid']
    edges = [
        ('Venice', 'Madrid'), 
        ('Lisbon', 'Reykjavik'), 
        ('Brussels', 'Venice'), 
        ('Venice', 'Santorini'), 
        ('Lisbon', 'Venice'), 
        ('Reykjavik', 'Madrid'), 
        ('Brussels', 'London'), 
        ('Madrid', 'London'), 
        ('Santorini', 'London'), 
        ('London', 'Reykjavik'), 
        ('Brussels', 'Lisbon'), 
        ('Lisbon', 'London'), 
        ('Lisbon', 'Madrid'), 
        ('Madrid', 'Santorini'), 
        ('Brussels', 'Reykjavik'), 
        ('Brussels', 'Madrid'), 
        ('Venice', 'London')
    ]
    
    flight_set = set()
    for u, v in edges:
        key = (min(u, v), max(u, v))
        flight_set.add(key)
    
    days = list(range(1, 18))
    p = {}
    for d in days:
        for c in cities:
            p[(d, c)] = Bool(f"p_{d}_{c}")
    
    s = Solver()
    
    for d in days:
        lst = [p[(d, c)] for c in cities]
        s.add(Or(lst))
        s.add(AtMost(*lst, 2))
        
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                edge_key = (min(c1, c2), max(c1, c2))
                if edge_key not in flight_set:
                    s.add(Not(And(p[(d, c1)], p[(d, c2)])))
    
    for d in range(1, 17):
        or_list = []
        for c in cities:
            or_list.append(And(p[(d, c)], p[(d+1, c)]))
        s.add(Or(or_list))
    
    s.add(p[(1, 'Brussels')])
    s.add(p[(2, 'Brussels')])
    
    total_days = {}
    for c in cities:
        total_days[c] = Sum([If(p[(d, c)], 1, 0) for d in days])
    
    s.add(total_days['Brussels'] == 2)
    s.add(total_days['Venice'] == 3)
    s.add(total_days['London'] == 3)
    s.add(total_days['Lisbon'] == 4)
    s.add(total_days['Reykjavik'] == 3)
    s.add(total_days['Santorini'] == 3)
    s.add(total_days['Madrid'] == 5)
    
    total_all = Sum([If(p[(d, c)], 1, 0) for d in days for c in cities])
    s.add(total_all == 23)
    
    venice_or = []
    for d in [5,6,7]:
        venice_or.append(p[(d, 'Venice')])
    s.add(Or(venice_or))
    
    madrid_or = []
    for d in [7,8,9,10,11]:
        madrid_or.append(p[(d, 'Madrid')])
    s.add(Or(madrid_or))
    
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        for d in days:
            cities_on_day = []
            for c in cities:
                if model.evaluate(p[(d, c)]):
                    cities_on_day.append(c)
            itinerary_list.append({"day": d, "place": cities_on_day})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()