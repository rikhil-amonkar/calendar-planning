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
    
    # Convert city names to indices
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    directed_flights = []
    for a, b in undirected_flights:
        idx_a = city_to_index[a]
        idx_b = city_to_index[b]
        directed_flights.append((idx_a, idx_b))
        directed_flights.append((idx_b, idx_a))
    
    s = Solver()
    num_days = 21
    x = [Int(f'x_{i}') for i in range(num_days)]
    
    # Constraint: Start in Stuttgart
    s.add(x[0] == stuttgart_index)
    
    # Constraint: End in Madrid (last two days)
    s.add(x[num_days-2] == madrid_index)
    s.add(x[num_days-1] == madrid_index)
    
    # Constraint: Madrid only in last two days
    for i in range(num_days - 2):
        s.add(x[i] != madrid_index)
    
    # Flight constraints between consecutive days
    for i in range(num_days - 1):
        same_city = (x[i] == x[i+1])
        valid_flight = Or([And(x[i] == a, x[i+1] == b) for (a, b) in directed_flights])
        s.add(Or(same_city, valid_flight))
    
    # Duration constraints per city
    for c in range(len(cities)):
        total_days = Sum([If(x[i] == c, 1, 0) for i in range(num_days)])
        s.add(total_days == required_days[c])
    
    if s.check() == sat:
        m = s.model()
        assignments = [m.eval(x[i]).as_long() for i in range(num_days)]
        
        # Group consecutive days in same city
        itinerary = []
        start_day = 1
        current_city = assignments[0]
        
        for day in range(1, num_days):
            if assignments[day] != current_city:
                end_day = day
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": cities[current_city]
                })
                start_day = day + 1
                current_city = assignments[day]
        
        # Add last segment
        itinerary.append({
            "day_range": f"Day {start_day}-{num_days}",
            "place": cities[current_city]
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()