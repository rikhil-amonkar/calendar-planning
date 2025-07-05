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
    
    # Create a solver instance
    s = Solver()
    
    # Variables: for each day, which city the traveler is in
    # For simplicity, we'll assume that on flight days, the traveler is in both cities
    # So we'll have a list of cities for each day
    day_cities = [[Bool(f'day_{day}_city_{city}') for city in cities] for day in range(1, total_days + 1)]
    
    # Constraints:
    # 1. Days 1-7 must be in Madrid
    for day in range(1, 8):
        s.add(day_cities[day - 1][city_map['Madrid']])
        for city in cities:
            if city != 'Madrid':
                s.add(Not(day_cities[day - 1][city_map[city]]))
    
    # 2. Days 14-15 must be in Bucharest
    for day in range(14, 16):
        s.add(day_cities[day - 1][city_map['Bucharest']])
        for city in cities:
            if city != 'Bucharest':
                s.add(Not(day_cities[day - 1][city_map[city]]))
    
    # 3. Total days in each city
    total_days_in_city = {city: 0 for city in cities}
    for city in cities:
        total_days_in_city[city] = Sum([If(day_cities[day - 1][city_map[city]], 1, 0) for day in range(1, total_days + 1)])
    
    s.add(total_days_in_city['Paris'] == 6)
    s.add(total_days_in_city['Madrid'] == 7)
    s.add(total_days_in_city['Bucharest'] == 2)
    s.add(total_days_in_city['Seville'] == 3)
    
    # 4. Flight constraints: if a day has more than one city, it must be a flight day
    # and the cities must have a direct flight
    for day in range(1, total_days + 1):
        cities_on_day = [day_cities[day - 1][city_map[city]] for city in cities]
        num_cities_on_day = Sum([If(city, 1, 0) for city in cities_on_day])
        
        # If more than one city on a day, it's a flight day
        s.add(Implies(num_cities_on_day > 1, num_cities_on_day == 2))
        
        # If it's a flight day, the two cities must have a direct flight
        for city1 in cities:
            for city2 in cities:
                if city1 != city2 and (city1, city2) not in direct_flights and (city2, city1) not in direct_flights:
                    s.add(Not(And(day_cities[day - 1][city_map[city1]], day_cities[day - 1][city_map[city2]])))
    
    # 5. Ensure that the traveler doesn't stay in a city for more than the required days
    # This is already handled by the total days constraints
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, total_days + 1):
            cities_on_day = []
            for city in cities:
                if m.evaluate(day_cities[day - 1][city_map[city]]):
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