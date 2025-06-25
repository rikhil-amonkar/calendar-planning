from z3 import *

def main():
    cities = ['Berlin', 'Stockholm', 'Nice', 'Lyon', 'Paris', 'Riga', 'Zurich', 'Seville', 'Milan', 'Naples']
    n_days = 23
    n_cities = len(cities)
    
    req = {
        'Lyon': 3,
        'Paris': 5,
        'Riga': 2,
        'Berlin': 2,
        'Stockholm': 3,
        'Zurich': 5,
        'Nice': 2,
        'Seville': 3,
        'Milan': 3,
        'Naples': 4
    }
    
    edges_list = [
        "Paris and Stockholm", "Seville and Paris", "Naples and Zurich", "Nice and Riga", "Berlin and Milan",
        "Paris and Zurich", "Paris and Nice", "Milan and Paris", "Milan and Riga", "Paris and Lyon",
        "Milan and Naples", "Paris and Riga", "Berlin and Stockholm", "Stockholm and Riga", "Nice and Zurich",
        "Milan and Zurich", "Lyon and Nice", "Zurich and Stockholm", "Zurich and Riga", "Berlin and Naples",
        "Milan and Stockholm", "Berlin and Zurich", "Milan and Seville", "Paris and Naples", "Berlin and Riga",
        "Nice and Stockholm", "Berlin and Paris", "Nice and Naples", "Berlin and Nice"
    ]
    
    directed_edges = set()
    for edge in edges_list:
        parts = edge.split(" and ")
        if len(parts) == 2:
            c1, c2 = parts
            idx1 = cities.index(c1)
            idx2 = cities.index(c2)
            directed_edges.add((idx1, idx2))
            directed_edges.add((idx2, idx1))
    
    base_city = [Int('base_city_%d' % i) for i in range(n_days+1)]
    flight_day = [Bool('flight_day_%d' % i) for i in range(1, n_days+1)]
    
    s = Solver()
    
    s.add(base_city[0] == cities.index('Berlin'))
    
    for i in range(0, n_days+1):
        s.add(base_city[i] >= 0, base_city[i] < n_cities)
    
    for i in range(1, n_days+1):
        idx = i - 1
        flight_today = flight_day[idx]
        no_flight = (base_city[i] == base_city[i-1])
        flight_constraints = []
        for (a, b) in directed_edges:
            flight_constraints.append(And(base_city[i-1] == a, base_city[i] == b))
        s.add(If(flight_today, And(base_city[i] != base_city[i-1], Or(flight_constraints)), no_flight))
    
    total_flight_days = Sum([If(flight_day[i], 1, 0) for i in range(0, n_days)])
    s.add(total_flight_days == 9)
    
    fixed_days = [
        (1, 'Berlin'),
        (2, 'Berlin'),
        (12, 'Nice'),
        (13, 'Nice'),
        (20, 'Stockholm'),
        (21, 'Stockholm'),
        (22, 'Stockholm')
    ]
    for (d, city_name) in fixed_days:
        c_index = cities.index(city_name)
        if d == 1:
            pass
        else:
            flight_today = flight_day[d-1]
            s.add(If(flight_today,
                     Or(base_city[d-1] == c_index, base_city[d] == c_index),
                     base_city[d-1] == c_index))
    
    for c_index in range(n_cities):
        city_name = cities[c_index]
        required_days = req[city_name]
        total_days = 0
        for d in range(1, n_days+1):
            total_days += If(base_city[d-1] == c_index, 1, 0)
        for d in range(1, n_days+1):
            total_days += If(And(flight_day[d-1], base_city[d] == c_index), 1, 0)
        s.add(total_days == required_days)
    
    if s.check() == sat:
        model = s.model()
        base_city_values = []
        for i in range(n_days+1):
            val = model[base_city[i]]
            if val is not None:
                base_city_values.append(val.as_long())
            else:
                base_city_values.append(0)
        
        flight_day_values = []
        for i in range(n_days):
            val = model[flight_day[i]]
            if val is not None:
                flight_day_values.append(is_true(val))
            else:
                flight_day_values.append(False)
        
        segments = []
        start = 1
        current = base_city_values[0]
        for i in range(1, n_days):
            if base_city_values[i] != current:
                end = i
                segments.append((start, end, current))
                start = i+1
                current = base_city_values[i]
        segments.append((start, n_days, base_city_values[n_days-1]))
        
        itinerary = []
        for (s, e, c_index) in segments:
            city_name = cities[c_index]
            if s == e:
                day_range_str = "Day %d" % s
            else:
                day_range_str = "Day %d-%d" % (s, e)
            itinerary.append({"day_range": day_range_str, "place": city_name})
        
        for day in range(1, n_days+1):
            if flight_day_values[day-1]:
                dep_city = cities[base_city_values[day-1]]
                arr_city = cities[base_city_values[day]]
                itinerary.append({"day_range": "Day %d" % day, "place": dep_city})
                itinerary.append({"day_range": "Day %d" % day, "place": arr_city})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()