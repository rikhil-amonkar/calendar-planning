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
    s_days = [Int(f's_{d}') for d in range(num_days)]
    e_days = [Int(f'e_{d}') for d in range(num_days)]
    
    for d in range(num_days):
        s.add(s_days[d] >= 0, s_days[d] < len(cities))
        s.add(e_days[d] >= 0, e_days[d] < len(cities))
    
    for d in range(num_days-1):
        s.add(s_days[d+1] == e_days[d])
    
    for d in range(num_days):
        same_city = (s_days[d] == e_days[d])
        valid_flight = Or([And(s_days[d] == a, e_days[d] == b) for (a, b) in directed_flights])
        s.add(Or(same_city, valid_flight))
    
    total_per_city = [0] * len(cities)
    for c in range(len(cities)):
        total = 0
        for d in range(num_days):
            in_city = Or(s_days[d] == c, e_days[d] == c)
            total += If(in_city, 1, 0)
        s.add(total == required_days[c])
    
    for d in range(19):
        s.add(Not(Or(s_days[d] == madrid_index, e_days[d] == madrid_index)))
    s.add(Or(s_days[19] == madrid_index, e_days[19] == madrid_index))
    s.add(Or(s_days[20] == madrid_index, e_days[20] == madrid_index))
    
    stuttgart_early = Or(
        Or(s_days[0] == stuttgart_index, e_days[0] == stuttgart_index),
        Or(s_days[1] == stuttgart_index, e_days[1] == stuttgart_index),
        Or(s_days[2] == stuttgart_index, e_days[2] == stuttgart_index),
        Or(s_days[3] == stuttgart_index, e_days[3] == stuttgart_index)
    )
    s.add(stuttgart_early)
    
    if s.check() == sat:
        m = s.model()
        end_cities = [m.eval(e_days[d]).as_long() for d in range(num_days)]
        
        itinerary = []
        current_city = end_cities[0]
        start_day = 1
        for day in range(1, num_days):
            if end_cities[day] != current_city:
                itinerary.append({
                    "day_range": f"Day {start_day}-{day}",
                    "place": cities[current_city]
                })
                current_city = end_cities[day]
                start_day = day + 1
        itinerary.append({
            "day_range": f"Day {start_day}-{num_days}",
            "place": cities[current_city]
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()