from z3 import *
import json

def main():
    # Define the City enum
    City = Datatype('City')
    City.declare('Paris')
    City.declare('Florence')
    City.declare('Vienna')
    City.declare('Porto')
    City.declare('Munich')
    City.declare('Nice')
    City.declare('Warsaw')
    City = City.create()

    city_dict = {
        'Paris': City.Paris,
        'Florence': City.Florence,
        'Vienna': City.Vienna,
        'Porto': City.Porto,
        'Munich': City.Munich,
        'Nice': City.Nice,
        'Warsaw': City.Warsaw
    }

    # Direct flight edges (undirected pairs)
    edges_str = [
        ('Florence', 'Vienna'),
        ('Paris', 'Warsaw'),
        ('Munich', 'Vienna'),
        ('Porto', 'Vienna'),
        ('Warsaw', 'Vienna'),
        ('Florence', 'Munich'),
        ('Munich', 'Warsaw'),
        ('Munich', 'Nice'),
        ('Paris', 'Florence'),
        ('Warsaw', 'Nice'),
        ('Porto', 'Munich'),
        ('Porto', 'Nice'),
        ('Paris', 'Vienna'),
        ('Nice', 'Vienna'),
        ('Porto', 'Paris'),
        ('Paris', 'Nice'),
        ('Paris', 'Munich'),
        ('Porto', 'Warsaw')
    ]
    
    # Create directed edges (both directions)
    directed_edges = []
    for (a, b) in edges_str:
        a_val = city_dict[a]
        b_val = city_dict[b]
        directed_edges.append((a_val, b_val))
        directed_edges.append((b_val, a_val))
    
    # Arrays for start_city and end_city for 20 days (index 0 to 19)
    start_city = [Const('start_city_%d' % i, City) for i in range(1, 21)]
    end_city = [Const('end_city_%d' % i, City) for i in range(1, 21)]
    
    s = Solver()
    
    # Constraint: For days 2 to 20, start_city[d] = end_city[d-1]
    for i in range(1, 20):
        s.add(start_city[i] == end_city[i-1])
    
    # Constraint: Flight connections
    for i in range(20):
        cond = Or([And(start_city[i] == a, end_city[i] == b) for (a, b) in directed_edges])
        s.add(Or(start_city[i] == end_city[i], cond))
    
    # Fixed event constraints
    # Porto on days 1,2,3 (indices 0,1,2)
    for i in [0, 1, 2]:
        s.add(Or(start_city[i] == city_dict['Porto'], end_city[i] == city_dict['Porto']))
    
    # Warsaw on days 13,14,15 (indices 12,13,14)
    for i in [12, 13, 14]:
        s.add(Or(start_city[i] == city_dict['Warsaw'], end_city[i] == city_dict['Warsaw']))
    
    # Vienna on days 19,20 (indices 18,19)
    for i in [18, 19]:
        s.add(Or(start_city[i] == city_dict['Vienna'], end_city[i] == city_dict['Vienna']))
    
    # Total days per city
    total_days = {}
    for city_name in city_dict:
        total = 0
        for i in range(20):
            total += If(Or(start_city[i] == city_dict[city_name], end_city[i] == city_dict[city_name]), 1, 0)
        s.add(total == {
            'Paris': 5,
            'Florence': 3,
            'Vienna': 2,
            'Porto': 3,
            'Munich': 5,
            'Nice': 5,
            'Warsaw': 3
        }[city_name])
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, 21):
            idx = day - 1
            start_val = m.eval(start_city[idx])
            end_val = m.eval(end_city[idx])
            cities = [str(start_val)]
            if start_val != end_val:
                cities.append(str(end_val))
            cities_sorted = sorted(cities)
            itinerary.append({"day": day, "place": cities_sorted})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()