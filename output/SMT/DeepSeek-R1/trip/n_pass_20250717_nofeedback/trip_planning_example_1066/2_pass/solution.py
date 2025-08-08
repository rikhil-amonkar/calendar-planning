from z3 import *
import json

def main():
    cities = ['Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Madrid', 'Helsinki', 'Split', 'London']
    required_days = [4, 3, 4, 2, 2, 5, 3, 5]
    madrid_index = cities.index('Madrid')
    stuttgart_index = cities.index('Stuttgart')
    
    undirected_flights = [
        ('Helsinki', 'London'),
        ('Split', 'Madrid'),
        ('Helsinki', 'Madrid'),
        ('London', 'Madrid'),
        ('Brussels', 'London'),
        ('Bucharest', 'London'),
        ('Brussels', 'Bucharest'),
        ('Bucharest', 'Madrid'),
        ('Split', 'Helsinki'),
        ('Mykonos', 'Madrid'),
        ('Stuttgart', 'London'),
        ('Helsinki', 'Brussels'),
        ('Brussels', 'Madrid'),
        ('Split', 'London'),
        ('Stuttgart', 'Split'),
        ('London', 'Mykonos')
    ]
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    undirected_flights_int = []
    for a, b in undirected_flights:
        undirected_flights_int.append((city_to_index[a], city_to_index[b]))
    
    directed_flights = []
    for (a, b) in undirected_flights_int:
        directed_flights.append((a, b))
        directed_flights.append((b, a))
    
    s = Solver()
    num_days = 21
    s_days = [Int(f's_{d}') for d in range(1, num_days+1)]
    e_days = [Int(f'e_{d}') for d in range(1, num_days+1)]
    
    for d in range(num_days):
        s.add(s_days[d] >= 0, s_days[d] < 8)
        s.add(e_days[d] >= 0, e_days[d] < 8)
    
    for d in range(num_days-1):
        s.add(s_days[d+1] == e_days[d])
    
    for d in range(num_days):
        no_travel = (s_days[d] == e_days[d])
        options = []
        for (a, b) in directed_flights:
            options.append(And(s_days[d] == a, e_days[d] == b))
        travel_ok = Or(options)
        s.add(Or(no_travel, travel_ok))
    
    total_per_city = [0] * 8
    for c in range(8):
        total = 0
        for d in range(num_days):
            in_city = Or(s_days[d] == c, And(s_days[d] != e_days[d], e_days[d] == c))
            total += If(in_city, 1, 0)
        total_per_city[c] = total
        s.add(total == required_days[c])
    
    for d in range(19):
        in_madrid = Or(s_days[d] == madrid_index, And(s_days[d] != e_days[d], e_days[d] == madrid_index))
        s.add(Not(in_madrid))
    in_madrid20 = Or(s_days[19] == madrid_index, And(s_days[19] != e_days[19], e_days[19] == madrid_index))
    in_madrid21 = Or(s_days[20] == madrid_index, And(s_days[20] != e_days[20], e_days[20] == madrid_index))
    s.add(in_madrid20, in_madrid21)
    
    stuttgart_early_days = []
    for d in range(4):
        in_stuttgart = Or(s_days[d] == stuttgart_index, And(s_days[d] != e_days[d], e_days[d] == stuttgart_index))
        stuttgart_early_days.append(in_stuttgart)
    s.add(Or(stuttgart_early_days))
    
    if s.check() == sat:
        m = s.model()
        counts = [0] * 8
        for d in range(num_days):
            s_val = m.eval(s_days[d]).as_long()
            e_val = m.eval(e_days[d]).as_long()
            for c in range(8):
                if s_val == c:
                    counts[c] += 1
                elif e_val == c and s_val != e_val:
                    counts[c] += 1
        valid = True
        for c in range(8):
            if counts[c] != required_days[c]:
                valid = False
                break
        if not valid:
            print('{"error": "No solution found"}')
            return
        
        itinerary_list = []
        for d in range(num_days):
            s_val = m.eval(s_days[d]).as_long()
            e_val = m.eval(e_days[d]).as_long()
            cities_today = {cities[s_val]}
            if s_val != e_val:
                cities_today.add(cities[e_val])
            place_str = ", ".join(sorted(cities_today))
            itinerary_list.append({"day": d+1, "place": place_str})
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()