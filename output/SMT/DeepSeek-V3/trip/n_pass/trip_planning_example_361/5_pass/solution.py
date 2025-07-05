from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Paris', 'Madrid', 'Bucharest', 'Seville']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights
    direct_flights = {
        ('Paris', 'Bucharest'),
        ('Seville', 'Paris'),
        ('Madrid', 'Bucharest'),
        ('Madrid', 'Paris'),
        ('Madrid', 'Seville')
    }
    
    # Total days
    total_days = 15
    
    # Create solver
    s = Solver()
    
    # Variables for each day and city
    day_cities = [[Bool(f'day_{day}_city_{city}') for city in cities] for day in range(1, total_days + 1)]
    
    # Constraints
    
    # 1. Days 1-7 must be in Madrid only
    for day in range(1, 8):
        s.add(day_cities[day-1][city_map['Madrid']])
        for city in cities:
            if city != 'Madrid':
                s.add(Not(day_cities[day-1][city_map[city]]))
    
    # 2. Day 8: Flight from Madrid to Paris (both cities)
    s.add(day_cities[7][city_map['Madrid']])
    s.add(day_cities[7][city_map['Paris']])
    for city in cities:
        if city not in ['Madrid', 'Paris']:
            s.add(Not(day_cities[7][city_map[city]]))
    
    # 3. Days 9-12: Paris only
    for day in range(9, 13):
        s.add(day_cities[day-1][city_map['Paris']])
        for city in cities:
            if city != 'Paris':
                s.add(Not(day_cities[day-1][city_map[city]]))
    
    # 4. Day 13: Flight from Paris to Seville (both cities)
    s.add(day_cities[12][city_map['Paris']])
    s.add(day_cities[12][city_map['Seville']])
    for city in cities:
        if city not in ['Paris', 'Seville']:
            s.add(Not(day_cities[12][city_map[city]]))
    
    # 5. Day 14: Flight from Seville to Bucharest (both cities)
    s.add(day_cities[13][city_map['Seville']])
    s.add(day_cities[13][city_map['Bucharest']])
    for city in cities:
        if city not in ['Seville', 'Bucharest']:
            s.add(Not(day_cities[13][city_map[city]]))
    
    # 6. Day 15: Bucharest only
    s.add(day_cities[14][city_map['Bucharest']])
    for city in cities:
        if city != 'Bucharest':
            s.add(Not(day_cities[14][city_map[city]]))
    
    # 7. Total days in each city
    total_days_in_city = {city: 0 for city in cities}
    for city in cities:
        total_days_in_city[city] = Sum([If(day_cities[day-1][city_map[city]], 1, 0) for day in range(1, total_days+1)])
    
    s.add(total_days_in_city['Paris'] == 6)
    s.add(total_days_in_city['Madrid'] == 7)
    s.add(total_days_in_city['Bucharest'] == 2)
    s.add(total_days_in_city['Seville'] == 3)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, total_days + 1):
            cities_on_day = []
            for city in cities:
                if m.evaluate(day_cities[day-1][city_map[city]]):
                    cities_on_day.append(city)
            if len(cities_on_day) == 1:
                itinerary.append({'day_range': f'Day {day}', 'place': cities_on_day[0]})
            else:
                for city in cities_on_day:
                    itinerary.append({'day_range': f'Day {day}', 'place': city})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

def main():
    result = solve_itinerary()
    print(result)

if __name__ == "__main__":
    main()