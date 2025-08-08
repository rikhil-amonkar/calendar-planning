from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Salzburg', 'Venice', 'Bucharest', 'Brussels', 'Hamburg', 'Copenhagen', 'Nice', 'Zurich', 'Naples']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list (corrected for consistency)
    direct_flights = {
        'Zurich': ['Brussels', 'Nice', 'Naples', 'Copenhagen', 'Bucharest', 'Venice'],
        'Brussels': ['Zurich', 'Venice', 'Bucharest', 'Hamburg', 'Nice', 'Copenhagen', 'Naples'],
        'Bucharest': ['Copenhagen', 'Brussels', 'Hamburg', 'Naples', 'Zurich'],
        'Venice': ['Brussels', 'Naples', 'Copenhagen', 'Zurich', 'Nice', 'Hamburg'],
        'Nice': ['Zurich', 'Hamburg', 'Brussels', 'Venice', 'Naples', 'Copenhagen'],
        'Hamburg': ['Nice', 'Bucharest', 'Brussels', 'Zurich', 'Copenhagen', 'Venice', 'Salzburg'],
        'Copenhagen': ['Bucharest', 'Brussels', 'Venice', 'Zurich', 'Hamburg', 'Naples', 'Nice'],
        'Naples': ['Zurich', 'Venice', 'Bucharest', 'Brussels', 'Copenhagen', 'Nice', 'Hamburg'],
        'Salzburg': ['Hamburg']
    }
    
    # Create a set of tuples for direct flights
    flight_pairs = set()
    for city, neighbors in direct_flights.items():
        for neighbor in neighbors:
            if (neighbor, city) not in flight_pairs:
                flight_pairs.add((city, neighbor))
    
    # Z3 solver
    s = Solver()
    
    # Variables: day 1 to 25, each is one of the cities
    days = [Int(f'day_{i}') for i in range(1, 26)]
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Helper functions
    def city_constraint(day, city):
        return days[day-1] == city_to_idx[city]
    
    def count_days_in_city(city):
        return Sum([If(days[i] == city_to_idx[city], 1, 0) for i in range(25)])
    
    # Fixed constraints:
    # Nice between day 9-11
    s.add(city_constraint(9, 'Nice'))
    s.add(city_constraint(10, 'Nice'))
    s.add(city_constraint(11, 'Nice'))
    
    # Copenhagen between day 18-21 (wedding)
    s.add(city_constraint(18, 'Copenhagen'))
    s.add(city_constraint(19, 'Copenhagen'))
    s.add(city_constraint(20, 'Copenhagen'))
    s.add(city_constraint(21, 'Copenhagen'))
    
    # Brussels between day 21-22 (meet friends)
    s.add(city_constraint(21, 'Brussels'))
    s.add(city_constraint(22, 'Brussels'))
    
    # Naples between day 22-25 (workshop)
    s.add(city_constraint(22, 'Naples'))
    s.add(city_constraint(23, 'Naples'))
    s.add(city_constraint(24, 'Naples'))
    s.add(city_constraint(25, 'Naples'))
    
    # Duration constraints:
    s.add(count_days_in_city('Salzburg') == 2)
    s.add(count_days_in_city('Venice') == 5)
    s.add(count_days_in_city('Bucharest') == 4)
    s.add(count_days_in_city('Brussels') == 2)  # days 21-22 already cover 2 days
    s.add(count_days_in_city('Hamburg') == 4)
    s.add(count_days_in_city('Copenhagen') == 4)  # days 18-21 cover 4 days
    s.add(count_days_in_city('Nice') == 3)  # days 9-11 cover 3 days
    s.add(count_days_in_city('Zurich') == 5)
    s.add(count_days_in_city('Naples') == 4)  # days 22-25 cover 4 days
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for i in range(24):
        current_day = days[i]
        next_day = days[i+1]
        # Either same city or connected by flight
        same_city = current_day == next_day
        flight_possible = Or([And(current_day == city_to_idx[city], next_day == city_to_idx[neighbor])
                             for city in direct_flights
                             for neighbor in direct_flights[city]])
        s.add(Or(same_city, flight_possible))
    
    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 26):
            city_idx = model.evaluate(days[day-1]).as_long()
            itinerary.append({'day': day, 'place': cities[city_idx]})
        
        # Output as JSON
        output = {'itinerary': itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

solve_itinerary()