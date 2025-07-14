from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Brussels', 'Venice', 'London', 'Lisbon', 'Reykjavik', 'Santorini', 'Madrid']
    city_vars = {city: [Bool(f'{city}_{day}') for day in range(1, 18)] for city in cities}
    
    # Direct flights
    direct_flights = {
        'Venice': ['Madrid', 'Brussels', 'Santorini', 'Lisbon', 'London'],
        'Lisbon': ['Reykjavik', 'Venice', 'London', 'Madrid'],
        'Brussels': ['Venice', 'London', 'Lisbon', 'Reykjavik', 'Madrid'],
        'Reykjavik': ['Lisbon', 'Madrid', 'London'],
        'Santorini': ['Venice', 'London', 'Madrid'],
        'Madrid': ['Venice', 'Reykjavik', 'London', 'Santorini', 'Lisbon'],
        'London': ['Brussels', 'Madrid', 'Santorini', 'Reykjavik', 'Lisbon', 'Venice']
    }
    
    s = Solver()
    
    # Each day must be in exactly one city (or two for flight days)
    for day in range(1, 18):
        # At least one city per day
        s.add(Or([city_vars[city][day-1] for city in cities]))
    
    # Fixed constraints
    # Brussels days 1-2
    s.add(city_vars['Brussels'][0])  # Day 1
    s.add(city_vars['Brussels'][1])  # Day 2
    
    # Venice between day 5 and 7 (i.e., at least one day in Venice between 5-7)
    s.add(Or([city_vars['Venice'][4], city_vars['Venice'][5], city_vars['Venice'][6]))  # Days 5,6,7 (0-based: 4,5,6)
    
    # Madrid wedding between day 7 and 11: at least one day in Madrid between 7-11
    s.add(Or([city_vars['Madrid'][6], city_vars['Madrid'][7], city_vars['Madrid'][8], city_vars['Madrid'][9], city_vars['Madrid'][10]))  # Days 7-11 (0-based: 6-10)
    
    # Total days per city
    city_days = {
        'Brussels': 2,
        'Venice': 3,
        'London': 3,
        'Lisbon': 4,
        'Reykjavik': 3,
        'Santorini': 3,
        'Madrid': 5
    }
    
    for city in cities:
        s.add(Sum([If(city_vars[city][d], 1, 0) for d in range(17)) == city_days[city])
    
    # Flight constraints: between two consecutive days, either stay in the same city or move to a directly connected city.
    for day in range(1, 17):
        current_day = day - 1
        next_day = day
        for city1 in cities:
            for city2 in cities:
                if city1 == city2:
                    continue
                s.add(Implies(
                    And(city_vars[city1][current_day], city_vars[city2][next_day]),
                    city2 in direct_flights[city1]
                ))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        day_to_cities = {}
        for day in range(1, 18):
            current_day = day - 1
            cities_in_day = []
            for city in cities:
                if is_true(model.eval(city_vars[city][current_day])):
                    cities_in_day.append(city)
            day_to_cities[day] = cities_in_day
        
        current_place = None
        current_start_day = None
        
        for day in range(1, 18):
            cities_in_day = day_to_cities[day]
            if len(cities_in_day) == 1:
                city = cities_in_day[0]
                if current_place is None:
                    current_place = city
                    current_start_day = day
                elif current_place == city:
                    continue
                else:
                    if current_start_day < day:
                        itinerary.append({
                            'day_range': f'Day {current_start_day}-{day-1}',
                            'place': current_place
                        })
                    else:
                        itinerary.append({
                            'day_range': f'Day {current_start_day}',
                            'place': current_place
                        })
                    itinerary.append({
                        'day_range': f'Day {day}',
                        'place': current_place
                    })
                    itinerary.append({
                        'day_range': f'Day {day}',
                        'place': city
                    })
                    current_place = city
                    current_start_day = day
            else:
                if current_place is not None:
                    if current_start_day < day:
                        itinerary.append({
                            'day_range': f'Day {current_start_day}-{day-1}',
                            'place': current_place
                        })
                    else:
                        itinerary.append({
                            'day_range': f'Day {current_start_day}',
                            'place': current_place
                        })
                city1, city2 = cities_in_day[0], cities_in_day[1]
                itinerary.append({
                    'day_range': f'Day {day}',
                    'place': city1
                })
                itinerary.append({
                    'day_range': f'Day {day}',
                    'place': city2
                })
                current_place = city2
                current_start_day = day + 1
        
        if current_place is not None and current_start_day <= 17:
            if current_start_day < 17:
                itinerary.append({
                    'day_range': f'Day {current_start_day}-17',
                    'place': current_place
                })
            else:
                itinerary.append({
                    'day_range': f'Day {current_start_day}',
                    'place': current_place
                })
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No solution found'}

result = solve_itinerary()
print(json.dumps(result, indent=2))