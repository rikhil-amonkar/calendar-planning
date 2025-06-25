from z3 import *
import json

def main():
    City, (Stockholm, Hamburg, Florence, Istanbul, Oslo, Vilnius, Santorini, Munich, Frankfurt, Krakow) = EnumSort('City', 
        ['Stockholm', 'Hamburg', 'Florence', 'Istanbul', 'Oslo', 'Vilnius', 'Santorini', 'Munich', 'Frankfurt', 'Krakow'])
    
    cities_list = [Stockholm, Hamburg, Florence, Istanbul, Oslo, Vilnius, Santorini, Munich, Frankfurt, Krakow]
    cities_names = ['Stockholm', 'Hamburg', 'Florence', 'Istanbul', 'Oslo', 'Vilnius', 'Santorini', 'Munich', 'Frankfurt', 'Krakow']
    
    dur = {
        Stockholm: 3,
        Hamburg: 5,
        Florence: 2,
        Istanbul: 5,
        Oslo: 5,
        Vilnius: 5,
        Santorini: 2,
        Munich: 5,
        Frankfurt: 4,
        Krakow: 5
    }
    
    bidirectional_pairs = [
        ("Oslo", "Stockholm"),
        ("Krakow", "Frankfurt"),
        ("Krakow", "Istanbul"),
        ("Munich", "Stockholm"),
        ("Hamburg", "Stockholm"),
        ("Oslo", "Istanbul"),
        ("Istanbul", "Stockholm"),
        ("Oslo", "Krakow"),
        ("Vilnius", "Istanbul"),
        ("Oslo", "Vilnius"),
        ("Frankfurt", "Istanbul"),
        ("Oslo", "Frankfurt"),
        ("Munich", "Hamburg"),
        ("Munich", "Istanbul"),
        ("Oslo", "Munich"),
        ("Frankfurt", "Florence"),
        ("Oslo", "Hamburg"),
        ("Vilnius", "Frankfurt"),
        ("Krakow", "Munich"),
        ("Hamburg", "Istanbul"),
        ("Frankfurt", "Stockholm"),
        ("Frankfurt", "Munich"),
        ("Krakow", "Stockholm"),
        ("Frankfurt", "Hamburg")
    ]
    
    one_way = [
        ("Krakow", "Vilnius"),
        ("Florence", "Munich"),
        ("Stockholm", "Santorini"),
        ("Santorini", "Oslo"),
        ("Vilnius", "Munich")
    ]
    
    name_to_city = {
        'Stockholm': Stockholm,
        'Hamburg': Hamburg,
        'Florence': Florence,
        'Istanbul': Istanbul,
        'Oslo': Oslo,
        'Vilnius': Vilnius,
        'Santorini': Santorini,
        'Munich': Munich,
        'Frankfurt': Frankfurt,
        'Krakow': Krakow
    }
    
    edges = set()
    for a, b in bidirectional_pairs:
        city_a = name_to_city[a]
        city_b = name_to_city[b]
        edges.add((city_a, city_b))
        edges.add((city_b, city_a))
    
    for a, b in one_way:
        city_a = name_to_city[a]
        city_b = name_to_city[b]
        edges.add((city_a, city_b))
    
    s = Solver()
    
    pos = [Const(f'pos_{i}', City) for i in range(10)]
    start_days = [Int(f's_{i}') for i in range(10)]
    end_days = [Int(f'e_{i}') for i in range(10)]
    
    s.add(Distinct(pos))
    
    s.add(start_days[0] == 1)
    s.add(end_days[9] == 32)
    
    for i in range(10):
        d_i = Int(f'd_{i}')
        d_i_val = If(
            pos[i] == Stockholm, 3,
            If(pos[i] == Hamburg, 5,
            If(pos[i] == Florence, 2,
            If(pos[i] == Istanbul, 5,
            If(pos[i] == Oslo, 5,
            If(pos[i] == Vilnius, 5,
            If(pos[i] == Santorini, 2,
            If(pos[i] == Munich, 5,
            If(pos[i] == Frankfurt, 4, 5)))))))))
        s.add(d_i == d_i_val)
        s.add(end_days[i] == start_days[i] + d_i_val - 1)
        if i < 9:
            s.add(start_days[i+1] == end_days[i])
    
    for i in range(10):
        s.add(If(pos[i] == Krakow, start_days[i] == 5, True))
        s.add(If(pos[i] == Istanbul, start_days[i] == 25, True))
    
    for i in range(9):
        conditions = []
        for (a, b) in edges:
            conditions.append(And(pos[i] == a, pos[i+1] == b))
        s.add(Or(conditions))
    
    for i in range(10):
        s.add(start_days[i] >= 1, start_days[i] <= 32)
        s.add(end_days[i] >= 1, end_days[i] <= 32)
    
    if s.check() == sat:
        m = s.model()
        pos_val = [m.evaluate(pos[i]) for i in range(10)]
        start_val = [m.evaluate(start_days[i]).as_long() for i in range(10)]
        end_val = [m.evaluate(end_days[i]).as_long() for i in range(10)]
        
        city_to_name = dict(zip(cities_list, cities_names))
        itinerary_list = []
        
        for i in range(10):
            city_name = city_to_name[pos_val[i]]
            s_i = start_val[i]
            e_i = end_val[i]
            itinerary_list.append({"day_range": f"Day {s_i}-{e_i}", "place": city_name})
            if i < 9:
                itinerary_list.append({"day_range": f"Day {e_i}", "place": city_name})
                next_city_name = city_to_name[pos_val[i+1]]
                itinerary_list.append({"day_range": f"Day {e_i}", "place": next_city_name})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()