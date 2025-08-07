import json
from z3 import *

def main():
    cities_list = ['Santorini', 'Krakow', 'Paris', 'Vilnius', 'Munich', 'Geneva', 'Amsterdam', 'Budapest', 'Split']
    days_dict = {
        'Santorini': 5,
        'Krakow': 5,
        'Paris': 5,
        'Vilnius': 3,
        'Munich': 5,
        'Geneva': 2,
        'Amsterdam': 4,
        'Budapest': 5,
        'Split': 4
    }
    city_to_int = {city: idx for idx, city in enumerate(cities_list)}
    int_to_city = {idx: city for idx, city in enumerate(cities_list)}

    bidirectional_pairs = [
        ("Paris", "Krakow"),
        ("Paris", "Amsterdam"),
        ("Paris", "Split"),
        ("Paris", "Geneva"),
        ("Amsterdam", "Geneva"),
        ("Split", "Krakow"),
        ("Munich", "Amsterdam"),
        ("Budapest", "Amsterdam"),
        ("Split", "Geneva"),
        ("Vilnius", "Split"),
        ("Munich", "Geneva"),
        ("Munich", "Krakow"),
        ("Vilnius", "Amsterdam"),
        ("Budapest", "Paris"),
        ("Krakow", "Amsterdam"),
        ("Vilnius", "Paris"),
        ("Budapest", "Geneva"),
        ("Split", "Amsterdam"),
        ("Santorini", "Geneva"),
        ("Amsterdam", "Santorini"),
        ("Munich", "Budapest"),
        ("Munich", "Paris")
    ]
    unidirectional_edges = [
        ("Vilnius", "Munich"),
        ("Krakow", "Vilnius")
    ]
    
    graph_edges = set()
    for a, b in bidirectional_pairs:
        u = city_to_int[a]
        v = city_to_int[b]
        graph_edges.add((u, v))
        graph_edges.add((v, u))
    for a, b in unidirectional_edges:
        u = city_to_int[a]
        v = city_to_int[b]
        graph_edges.add((u, v))
    
    s = Solver()
    pos = {city: Int(f'pos_{city}') for city in cities_list}
    
    for city in cities_list:
        s.add(pos[city] >= 0, pos[city] < 9)
    s.add(Distinct([pos[city] for city in cities_list]))
    
    for i in range(8):
        constraints = []
        for c1 in cities_list:
            for c2 in cities_list:
                if c1 == c2:
                    continue
                u = city_to_int[c1]
                v = city_to_int[c2]
                if (u, v) in graph_edges:
                    constraints.append(And(pos[c1] == i, pos[c2] == i+1))
        if constraints:
            s.add(Or(constraints))
        else:
            s.add(False)
    
    start_day_expr = {}
    for city in cities_list:
        terms = []
        for d in cities_list:
            terms.append(If(pos[d] < pos[city], days_dict[d], 0))
        total_before = Sum(terms)
        start_day_expr[city] = 1 + total_before - pos[city]
    
    s.add(start_day_expr['Santorini'] >= 21, start_day_expr['Santorini'] <= 29)
    s.add(start_day_expr['Krakow'] >= 14, start_day_expr['Krakow'] <= 22)
    s.add(start_day_expr['Paris'] >= 7, start_day_expr['Paris'] <= 15)
    
    if s.check() == sat:
        m = s.model()
        pos_val = {city: m.eval(pos[city]).as_long() for city in cities_list}
        ordered_cities = sorted(cities_list, key=lambda c: pos_val[c])
        
        start_days = []
        total_prev = 0
        for i, city in enumerate(ordered_cities):
            start_day = 1 + total_prev - i
            start_days.append(start_day)
            total_prev += days_dict[city]
        
        itinerary = []
        for day in range(1, 31):
            places = []
            for i, city in enumerate(ordered_cities):
                start_day = start_days[i]
                end_day = start_day + days_dict[city] - 1
                if start_day <= day <= end_day:
                    places.append(city)
            itinerary.append({"day": day, "place": places})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()