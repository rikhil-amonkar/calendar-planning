from z3 import *
import json

def main():
    cities = ['Venice', 'Reykjavik', 'Munich', 'Santorini', 'Manchester', 'Porto', 'Bucharest', 'Tallinn', 'Valencia', 'Vienna']
    
    durations = {
        'Venice': 3,
        'Reykjavik': 2,
        'Munich': 3,
        'Santorini': 3,
        'Manchester': 3,
        'Porto': 3,
        'Bucharest': 5,
        'Tallinn': 4,
        'Valencia': 2,
        'Vienna': 5
    }
    
    fixed_events = {
        'Munich': (4, 6),
        'Santorini': (8, 10),
        'Valencia': (14, 15)
    }
    
    flight_list = [
        ('Bucharest', 'Manchester'),
        ('Munich', 'Venice'),
        ('Santorini', 'Manchester'),
        ('Vienna', 'Reykjavik'),
        ('Venice', 'Santorini'),
        ('Munich', 'Porto'),
        ('Valencia', 'Vienna'),
        ('Manchester', 'Vienna'),
        ('Porto', 'Vienna'),
        ('Venice', 'Manchester'),
        ('Santorini', 'Vienna'),
        ('Munich', 'Manchester'),
        ('Munich', 'Reykjavik'),
        ('Bucharest', 'Valencia'),
        ('Venice', 'Vienna'),
        ('Bucharest', 'Vienna'),
        ('Porto', 'Manchester'),
        ('Munich', 'Vienna'),
        ('Valencia', 'Porto'),
        ('Munich', 'Bucharest'),
        ('Tallinn', 'Munich'),
        ('Santorini', 'Bucharest'),
        ('Munich', 'Valencia')
    ]
    
    flight_set = set()
    for a, b in flight_list:
        flight_set.add((a, b))
        flight_set.add((b, a))
    
    CitySort, city_consts = EnumSort('City', cities)
    city_map = {name: const for name, const in zip(cities, city_consts)}
    
    s = Solver()
    
    c = [Const(f'c_{i}', CitySort) for i in range(10)]
    start = [Int(f'start_{i}') for i in range(10)]
    end = [Int(f'end_{i}') for i in range(10)]
    
    s.add(start[0] == 1)
    s.add(end[9] == 24)
    for i in range(9):
        s.add(start[i+1] == end[i])
    
    for i in range(10):
        dur_expr = Int(f'dur_{i}')
        dur_cases = []
        for city in cities:
            cond = (c[i] == city_map[city])
            dur_val = durations[city]
            dur_cases.append((cond, dur_val))
        duration_i = dur_cases[0][1]
        for j in range(1, len(dur_cases)):
            cond, val = dur_cases[j]
            duration_i = If(cond, val, duration_i)
        s.add(duration_i == (end[i] - start[i] + 1))
    
    for i in range(10):
        for city, (s_fixed, e_fixed) in fixed_events.items():
            s.add(If(c[i] == city_map[city], And(start[i] == s_fixed, end[i] == e_fixed), True))
    
    s.add(Distinct(c))
    
    for i in range(9):
        constraints = []
        for a, b in flight_set:
            constraints.append(And(c[i] == city_map[a], c[i+1] == city_map[b]))
        s.add(Or(constraints))
    
    for i in range(10):
        s.add(start[i] >= 1)
        s.add(end[i] <= 24)
        s.add(start[i] <= end[i])
    
    if s.check() == sat:
        model = s.model()
        seq = []
        start_vals = []
        end_vals = []
        for i in range(10):
            city_val = model.evaluate(c[i])
            for city in cities:
                if city_val.eq(city_map[city]):
                    seq.append(city)
                    break
            start_vals.append(model.evaluate(start[i]).as_long())
            end_vals.append(model.evaluate(end[i]).as_long())
        
        itinerary_list = []
        for day in range(1, 25):
            for i in range(10):
                if start_vals[i] <= day <= end_vals[i]:
                    itinerary_list.append({"day": day, "place": seq[i]})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()