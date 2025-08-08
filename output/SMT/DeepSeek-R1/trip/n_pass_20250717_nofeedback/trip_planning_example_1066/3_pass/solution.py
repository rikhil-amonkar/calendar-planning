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
            in_city = Or(s_days[d] == c, e_days[d] == c)
            total += If(in_city, 1, 0)
        total_per_city[c] = total
        s.add(total == required_days[c])
    
    for d in range(19):
        in_madrid = Or(s_days[d] == madrid_index, e_days[d] == madrid_index)
        s.add(Not(in_madrid))
    in_madrid20 = Or(s_days[19] == madrid_index, e_days[19] == madrid_index)
    in_madrid21 = Or(s_days[20] == madrid_index, e_days[20] == madrid_index)
    s.add(in_madrid20, in_madrid21)
    
    stuttgart_early_days = []
    for d in range(4):
        in_stuttgart = Or(s_days[d] == stuttgart_index, e_days[d] == stuttgart_index)
        stuttgart_early_days.append(in_stuttgart)
    s.add(Or(stuttgart_early_days))
    
    if s.check() == sat:
        m = s.model()
        end_cities = []
        for d in range(num_days):
            e_val = m.eval(e_days[d]).as_long()
            end_cities.append(e_val)
        
        itinerary_list = []
        current_city = end_cities[0]
        start_day = 1
        end_day = 1
        for d in range(1, num_days):
            if end_cities[d] == current_city:
                end_day = d + 1
            else:
                itinerary_list.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": cities[current_city]
                })
                current_city = end_cities[d]
                start_day = d + 1
                end_day = d + 1
        itinerary_list.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": cities[current_city]
        })
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()