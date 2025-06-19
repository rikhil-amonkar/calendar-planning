from z3 import *
import json

def main():
    cities = ['Reykjavik', 'Riga', 'Warsaw', 'Istanbul', 'Krakow']
    dur = {
        'Reykjavik': 7,
        'Riga': 2,
        'Warsaw': 3,
        'Istanbul': 6,
        'Krakow': 7
    }
    
    flight_set = { 
        ('Istanbul', 'Krakow'), 
        ('Warsaw', 'Reykjavik'),
        ('Istanbul', 'Warsaw'),
        ('Riga', 'Istanbul'),
        ('Krakow', 'Warsaw'),
        ('Riga', 'Warsaw')
    }
    
    allowed_edges = []
    for (c1, c2) in flight_set:
        allowed_edges.append((c1, c2))
        allowed_edges.append((c2, c1))
    
    # Create solver and variables
    s = Solver()
    city_vars = [String(f'city_{i}') for i in range(5)]
    start_days = [Int(f'start_{i}') for i in range(5)]
    
    # Each city_vars must be one of the cities and all distinct
    for i in range(5):
        s.add(Or(*[city_vars[i] == c for c in cities]))
    s.add(Distinct(city_vars))
    
    # Flight constraints between consecutive cities
    for i in range(4):
        edge_constraints = []
        for (c1, c2) in allowed_edges:
            edge_constraints.append(And(city_vars[i] == c1, city_vars[i+1] == c2))
        s.add(Or(edge_constraints))
    
    # Start day constraints
    s.add(start_days[0] == 1)
    for i in range(4):
        dur_i = Int(f'dur_{i}')
        s.add(dur_i == If(city_vars[i] == 'Reykjavik', dur['Reykjavik'],
                        If(city_vars[i] == 'Riga', dur['Riga'],
                        If(city_vars[i] == 'Warsaw', dur['Warsaw'],
                        If(city_vars[i] == 'Istanbul', dur['Istanbul'],
                        dur['Krakow']))))
        s.add(start_days[i+1] == start_days[i] + dur_i - 1)
    
    dur_last = Int('dur_last')
    s.add(dur_last == If(city_vars[4] == 'Reykjavik', dur['Reykjavik'],
                       If(city_vars[4] == 'Riga', dur['Riga'],
                       If(city_vars[4] == 'Warsaw', dur['Warsaw'],
                       If(city_vars[4] == 'Istanbul', dur['Istanbul'],
                       dur['Krakow']))))
    s.add(start_days[4] + dur_last - 1 == 21)
    
    # Event constraints
    for i in range(5):
        s.add(If(city_vars[i] == 'Riga', Or(start_days[i] == 1, start_days[i] == 2), True))
        s.add(If(city_vars[i] == 'Istanbul', start_days[i] <= 7, True))
    
    if s.check() == sat:
        m = s.model()
        order = [m.eval(city_vars[i]).as_string() for i in range(5)]
        starts = [m.eval(start_days[i]).as_long() for i in range(5)]
        
        itinerary = []
        for i in range(5):
            c = order[i]
            start = starts[i]
            d = dur[c]
            end = start + d - 1
            itinerary.append({"day_range": f"Day {start}-{end}", "place": c})
            if i < 4:
                itinerary.append({"day_range": f"Day {end}", "place": c})
                itinerary.append({"day_range": f"Day {end}", "place": order[i+1]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()