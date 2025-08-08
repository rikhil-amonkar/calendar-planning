from z3 import *

def main():
    cities = ['Frankfurt', 'Salzburg', 'Athens', 'Reykjavik', 'Bucharest', 'Valencia', 'Vienna', 'Amsterdam', 'Stockholm', 'Riga']
    durations = {
        'Frankfurt': 4,
        'Salzburg': 5,
        'Athens': 5,
        'Reykjavik': 5,
        'Bucharest': 3,
        'Valencia': 2,
        'Vienna': 5,
        'Amsterdam': 3,
        'Stockholm': 3,
        'Riga': 3
    }
    
    flight_pairs = []
    undirected = [
        ('Valencia', 'Frankfurt'),
        ('Vienna', 'Bucharest'),
        ('Athens', 'Bucharest'),
        ('Riga', 'Frankfurt'),
        ('Stockholm', 'Athens'),
        ('Amsterdam', 'Bucharest'),
        ('Amsterdam', 'Frankfurt'),
        ('Stockholm', 'Vienna'),
        ('Amsterdam', 'Reykjavik'),
        ('Reykjavik', 'Frankfurt'),
        ('Stockholm', 'Amsterdam'),
        ('Amsterdam', 'Valencia'),
        ('Vienna', 'Frankfurt'),
        ('Valencia', 'Bucharest'),
        ('Bucharest', 'Frankfurt'),
        ('Stockholm', 'Frankfurt'),
        ('Valencia', 'Vienna'),
        ('Frankfurt', 'Salzburg'),
        ('Amsterdam', 'Vienna'),
        ('Stockholm', 'Reykjavik'),
        ('Amsterdam', 'Riga'),
        ('Stockholm', 'Riga'),
        ('Vienna', 'Reykjavik'),
        ('Amsterdam', 'Athens'),
        ('Athens', 'Frankfurt'),
        ('Vienna', 'Athens'),
        ('Riga', 'Bucharest')
    ]
    for (a, b) in undirected:
        flight_pairs.append((a, b))
        flight_pairs.append((b, a))
    directed = [
        ('Valencia', 'Athens'),
        ('Athens', 'Riga'),
        ('Reykjavik', 'Athens')
    ]
    flight_pairs.extend(directed)
    
    CitySort, city_consts = EnumSort('City', cities)
    city_dict = {name: const for name, const in zip(cities, city_consts)}
    duration_arr = {city_dict[city]: durations[city] for city in cities}
    
    s = Solver()
    order = [Const('order{}'.format(i), CitySort) for i in range(10)]
    s.add(Distinct(order))
    
    C = [Int('C_{}'.format(i)) for i in range(10)]
    for i in range(10):
        if i == 0:
            s.add(C[i] == duration_arr[order[i]])
        else:
            s.add(C[i] == C[i-1] + duration_arr[order[i]] - 1)
    s.add(C[9] == 29)
    
    for i in range(10):
        start_i = If(i == 0, 1, C[i-1])
        end_i = C[i]
        s.add(If(order[i] == city_dict['Valencia'], And(start_i == 5, end_i == 6), True))
        s.add(If(order[i] == city_dict['Stockholm'], start_i <= 3, True))
        s.add(If(order[i] == city_dict['Vienna'], And(start_i <= 10, end_i >= 6), True))
        s.add(If(order[i] == city_dict['Athens'], And(start_i <= 18, end_i >= 14), True))
        s.add(If(order[i] == city_dict['Riga'], And(start_i <= 20, end_i >= 18), True))
    
    for i in range(9):
        or_conditions = []
        for (a, b) in flight_pairs:
            cond = And(order[i] == city_dict[a], order[i+1] == city_dict[b])
            or_conditions.append(cond)
        s.add(Or(or_conditions))
    
    if s.check() == sat:
        model = s.model()
        order_val = [model[order[i]] for i in range(10)]
        start_days = {}
        end_days = {}
        C_val = [0] * 10
        for i in range(10):
            if i == 0:
                C_val[i] = model.evaluate(C[i]).as_long()
            else:
                C_val[i] = model.evaluate(C[i]).as_long()
        for i in range(10):
            city_name = None
            for name, const in city_dict.items():
                if model.evaluate(order[i]) == model.evaluate(const):
                    city_name = name
                    break
            if i == 0:
                start_day = 1
                end_day = C_val[0]
            else:
                start_day = C_val[i-1]
                end_day = C_val[i]
            start_days[city_name] = start_day
            end_days[city_name] = end_day
        
        itinerary = []
        for day in range(1, 30):
            cities_today = []
            for city in cities:
                if start_days[city] <= day <= end_days[city]:
                    cities_today.append(city)
            itinerary.append({'day': day, 'city': cities_today})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()