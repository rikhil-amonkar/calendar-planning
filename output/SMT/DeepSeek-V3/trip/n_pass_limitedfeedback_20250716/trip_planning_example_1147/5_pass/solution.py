from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Brussels', 'Helsinki', 'Split', 'Dubrovnik', 'Istanbul', 'Milan', 'Vilnius', 'Frankfurt']
    city_vars = {city: [Bool(f'{city}_{day}') for day in range(1, 23)] for city in cities}
    
    # Corrected direct flights (undirected)
    direct_flights = {
        'Milan': ['Frankfurt', 'Split', 'Vilnius', 'Brussels', 'Helsinki', 'Istanbul'],
        'Split': ['Frankfurt', 'Milan', 'Helsinki', 'Vilnius'],
        'Brussels': ['Vilnius', 'Helsinki', 'Istanbul', 'Milan', 'Frankfurt'],
        'Helsinki': ['Brussels', 'Istanbul', 'Vilnius', 'Dubrovnik', 'Frankfurt', 'Split', 'Milan'],
        'Istanbul': ['Brussels', 'Helsinki', 'Dubrovnik', 'Milan', 'Frankfurt', 'Vilnius'],
        'Dubrovnik': ['Helsinki', 'Istanbul', 'Frankfurt'],
        'Frankfurt': ['Milan', 'Split', 'Brussels', 'Helsinki', 'Dubrovnik', 'Istanbul', 'Vilnius'],
        'Vilnius': ['Brussels', 'Milan', 'Helsinki', 'Split', 'Frankfurt', 'Istanbul']
    }
    
    s = Solver()
    
    # Each day, the traveler is in at least one city (could be two if it's a flight day)
    for day in range(1, 23):
        s.add(Or([city_vars[city][day-1] for city in cities]))
    
    # Flight day constraints
    for day in range(1, 23):
        for city1 in cities:
            for city2 in cities:
                if city1 != city2:
                    s.add(Implies(And(city_vars[city1][day-1], city_vars[city2][day-1]),
                                (city2 in direct_flights[city1])))
    
    # No more than two cities per day
    for day in range(1, 23):
        s.add(Sum([If(city_vars[city][day-1], 1, 0) for city in cities]) <= 2)
    
    # Total days per city
    city_days = {
        'Brussels': 3,
        'Helsinki': 3,
        'Split': 4,
        'Dubrovnik': 2,
        'Istanbul': 5,
        'Milan': 4,
        'Vilnius': 5,
        'Frankfurt': 3
    }
    for city in cities:
        s.add(Sum([If(city_vars[city][day-1], 1, 0) for day in range(1, 23)]) == city_days[city])
    
    # Fixed events
    # Istanbul: days 1-5 (must be there on these days)
    for day in range(1, 6):
        s.add(city_vars['Istanbul'][day-1])
    
    # Vilnius: workshop between day 18-22 (must be there at least one day in this range)
    s.add(Or([city_vars['Vilnius'][day-1] for day in range(18, 23)]))
    
    # Frankfurt: wedding between day 16-18 (must be there at least one day in this range)
    s.add(Or([city_vars['Frankfurt'][day-1] for day in range(16, 19)]))
    
    # Solve the model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        
        for day in range(1, 23):
            cities_today = [city for city in cities if is_true(model[city_vars[city][day-1]])]
            
            if len(cities_today) == 1:
                place = cities_today[0]
                if place != current_place:
                    if current_place is not None:
                        itinerary.append({'day_range': f'Day {start_day}-{day-1}', 'place': current_place})
                    current_place = place
                    start_day = day
            else:
                if current_place is not None:
                    itinerary.append({'day_range': f'Day {start_day}-{day-1}', 'place': current_place})
                itinerary.append({'day_range': f'Day {day}-{day}', 'place': f"{cities_today[0]}/{cities_today[1]}"})
                current_place = None
                start_day = day + 1
        
        if current_place is not None:
            itinerary.append({'day_range': f'Day {start_day}-22', 'place': current_place})
        
        # Verify all constraints
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            days = entry['day_range'].split('Day ')[1].split('-')
            start = int(days[0])
            end = int(days[1])
            duration = end - start + 1
            
            if '/' in entry['place']:
                city1, city2 = entry['place'].split('/')
                day_counts[city1] += 1
                day_counts[city2] += 1
            else:
                day_counts[entry['place']] += duration
        
        for city, required in city_days.items():
            assert day_counts[city] == required, f"Day count mismatch for {city}"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))