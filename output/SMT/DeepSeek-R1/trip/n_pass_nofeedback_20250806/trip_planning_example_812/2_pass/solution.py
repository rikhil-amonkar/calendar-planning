from z3 import *
import json

def main():
    # Define the City enum using EnumSort
    City, cities = EnumSort('City', ['Paris', 'Florence', 'Vienna', 'Porto', 'Munich', 'Nice', 'Warsaw'])
    Paris, Florence, Vienna, Porto, Munich, Nice, Warsaw = cities

    city_dict = {
        'Paris': Paris,
        'Florence': Florence,
        'Vienna': Vienna,
        'Porto': Porto,
        'Munich': Munich,
        'Nice': Nice,
        'Warsaw': Warsaw
    }

    # Direct flight edges (undirected pairs) in both directions
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
    
    # Create directed edges
    directed_edges = []
    for a, b in edges_str:
        a_val = city_dict[a] if a in city_dict else None
        b_val = city_dict[b] if b in city_dict else None
        if a_val is not None and b_val is not None:
            directed_edges.append((a_val, b_val))
            directed_edges.append((b_val, a_val))
    
    # Arrays for start_city and end_city for 20 days (index 0 to 19)
    start_city = [Const('start_city_%d' % i, City) for i in range(20)]
    end_city = [Const('end_city_%d' % i, City) for i in range(20)]
    
    s = Solver()
    
    # Constraint: For days 1 to 19, end_city[i] == start_city[i+1]
    for i in range(19):
        s.add(end_city[i] == start_city[i+1])
    
    # Constraint: Flight connections - if start != end, must be direct flight
    for i in range(20):
        same_city = (start_city[i] == end_city[i])
        flight_possible = Or([And(start_city[i] == a, end_city[i] == b) for (a, b) in directed_edges])
        s.add(Or(same_city, flight_possible))
    
    # Fixed event constraints
    # Porto on days 1-3 (indices 0,1,2)
    for i in [0, 1, 2]:
        s.add(Or(start_city[i] == Porto, end_city[i] == Porto))
    
    # Warsaw on days 13-15 (indices 12,13,14)
    for i in [12, 13, 14]:
        s.add(Or(start_city[i] == Warsaw, end_city[i] == Warsaw))
    
    # Vienna on days 19-20 (indices 18,19)
    for i in [18, 19]:
        s.add(Or(start_city[i] == Vienna, end_city[i] == Vienna))
    
    # Total days per city
    total_days = {}
    city_names = ['Paris', 'Florence', 'Vienna', 'Porto', 'Munich', 'Nice', 'Warsaw']
    required_days = {
        'Paris': 5,
        'Florence': 3,
        'Vienna': 2,
        'Porto': 3,
        'Munich': 5,
        'Nice': 5,
        'Warsaw': 3
    }
    for cname in city_names:
        c = city_dict[cname]
        total = 0
        for i in range(20):
            total += If(Or(start_city[i] == c, end_city[i] == c), 1, 0)
        s.add(total == required_days[cname])
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names_map = {
            Paris: "Paris",
            Florence: "Florence",
            Vienna: "Vienna",
            Porto: "Porto",
            Munich: "Munich",
            Nice: "Nice",
            Warsaw: "Warsaw"
        }
        for day in range(1, 21):
            idx = day - 1
            start_val = m.eval(start_city[idx])
            end_val = m.eval(end_city[idx])
            cities_list = [city_names_map[start_val]]
            if start_val != end_val:
                cities_list.append(city_names_map[end_val])
            cities_list_sorted = sorted(cities_list)
            itinerary.append({"day": day, "place": cities_list_sorted})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()