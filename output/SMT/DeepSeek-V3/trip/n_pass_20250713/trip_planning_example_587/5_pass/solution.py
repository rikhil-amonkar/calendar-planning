from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ['Manchester', 'Istanbul', 'Venice', 'Krakow', 'Lyon']
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    flights = [
        ('Manchester', 'Venice'),
        ('Manchester', 'Istanbul'),
        ('Manchester', 'Krakow'),
        ('Venice', 'Istanbul'),
        ('Venice', 'Lyon'),
        ('Istanbul', 'Krakow'),
        ('Istanbul', 'Lyon')
    ]
    
    # Create adjacency list
    adjacency = {city: set() for city in cities}
    for a, b in flights:
        adjacency[a].add(b)
        adjacency[b].add(a)
    
    total_days = 21
    required_days = {
        'Manchester': 3,
        'Istanbul': 7,
        'Venice': 7,
        'Krakow': 6,
        'Lyon': 2
    }
    
    # Decision variables
    day_city = [Int(f'day_{day}') for day in range(total_days)]
    s = Solver()
    
    # Each day must be assigned to a valid city
    for day in range(total_days):
        s.add(day_city[day] >= 0, day_city[day] < len(cities))
    
    # Wedding in Manchester days 1-3 (0-based days 0-2)
    for day in [0, 1, 2]:
        s.add(day_city[day] == city_idx['Manchester'])
    
    # Workshop in Venice between days 3-9 (0-based days 2-8)
    s.add(Or([day_city[day] == city_idx['Venice'] for day in range(2, 9)]))
    
    # Flight constraints between consecutive days
    for day in range(total_days - 1):
        current = day_city[day]
        next_day = day_city[day + 1]
        # Either stay in same city or take a direct flight
        s.add(Or(
            current == next_day,
            *[And(current == city_idx[a], next_day == city_idx[b]) 
              for a, b in flights]
        ))
    
    # Total days per city
    for city in cities:
        s.add(Sum([If(day_city[day] == city_idx[city], 1, 0) 
                 for day in range(total_days)]) == required_days[city]
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        
        for day in range(total_days):
            city = cities[model.evaluate(day_city[day]).as_long()]
            
            if day == 0:
                current_city = city
                start_day = 1
            else:
                prev_city = cities[model.evaluate(day_city[day - 1]).as_long()]
                if city != prev_city:
                    # Add previous stay
                    itinerary.append({
                        'day_range': f'Day {start_day}-{day}',
                        'place': prev_city
                    })
                    # Add flight day records
                    itinerary.append({
                        'day_range': f'Day {day}',
                        'place': prev_city
                    })
                    itinerary.append({
                        'day_range': f'Day {day}',
                        'place': city
                    })
                    current_city = city
                    start_day = day + 1
        
        # Add final stay
        itinerary.append({
            'day_range': f'Day {start_day}-{total_days}',
            'place': current_city
        })
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate and print itinerary
import json
print(json.dumps(solve_itinerary(), indent=2))