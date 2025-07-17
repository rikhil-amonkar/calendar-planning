from z3 import *

def solve_itinerary():
    # Cities
    Prague, Berlin, Tallinn, Stockholm = Ints('Prague Berlin Tallinn Stockholm')
    cities = [Prague, Berlin, Tallinn, Stockholm]
    city_names = {Prague: 'Prague', Berlin: 'Berlin', Tallinn: 'Tallinn', Stockholm: 'Stockholm'}
    
    # Days are 1..12
    days = 12
    # For each day, which city are we in?
    day_city = [Int(f'day_{i+1}') for i in range(days)]
    
    s = Solver()
    
    # Each day_city must be one of the four cities
    for day in day_city:
        s.add(Or([day == city for city in cities]))
    
    # Direct flights: possible transitions between cities
    direct_flights = {
        Prague: [Tallinn, Stockholm],
        Berlin: [Tallinn, Stockholm],
        Tallinn: [Prague, Berlin, Stockholm],
        Stockholm: [Prague, Berlin, Tallinn]
    }
    
    # Constraint: transitions between days must be via direct flights or staying in the same city
    for i in range(days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        s.add(Or(next_city == current_city, Or([next_city == dest for dest in direct_flights[current_city]])))
    
    # Total days in each city
    def count_days(city):
        return Sum([If(day_city[i] == city, 1, 0) for i in range(days)])
    
    s.add(count_days(Prague) == 2)
    s.add(count_days(Berlin) == 3)
    s.add(count_days(Tallinn) == 5)
    s.add(count_days(Stockholm) == 5)
    
    # Specific day constraints
    # Day 6 and 8 must be Berlin (1-based)
    s.add(day_city[5] == Berlin)  # day 6
    s.add(day_city[7] == Berlin)  # day 8
    
    # Days 9-12 must be Tallinn (1-based)
    for i in range(8, 12):
        s.add(day_city[i] == Tallinn)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_val = m.evaluate(day_city[i]).as_long()
            city_name = city_names[city_val]
            itinerary.append({'day': day_num, 'place': city_name})
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))