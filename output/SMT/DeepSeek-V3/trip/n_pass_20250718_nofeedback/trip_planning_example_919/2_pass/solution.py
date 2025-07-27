from z3 import *

def solve_itinerary():
    # Define the cities and their codes for easier reference
    cities = {
        'Vienna': 0,
        'Milan': 1,
        'Rome': 2,
        'Riga': 3,
        'Lisbon': 4,
        'Vilnius': 5,
        'Oslo': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 5, 4, 3, 2, 6],  # Vienna
        1: [0, 3, 6, 4, 5],      # Milan
        2: [6, 3, 4, 0],          # Rome
        3: [6, 0, 1, 5, 4, 2],    # Riga
        4: [0, 6, 2, 1, 3],       # Lisbon
        5: [0, 6, 3, 1],          # Vilnius
        6: [3, 2, 4, 1, 0, 5]     # Oslo
    }
    
    # Create Z3 solver instance
    s = Solver()
    
    # Variables: for each day, which city is the person in?
    # day_city[d] represents the city on day d (1-based)
    day_city = [Int(f"day_{day}_city") for day in range(1, 16)]
    
    # Constraints:
    
    # 1. Each day's city must be one of the valid cities (0-6)
    for day in range(15):
        s.add(day_city[day] >= 0, day_city[day] <= 6)
    
    # 2. Fixed days:
    # Day 1 and 4 must be in Vienna (conference)
    s.add(day_city[0] == cities['Vienna'])
    s.add(day_city[3] == cities['Vienna'])
    
    # Relatives in Lisbon between day 11-13 (days 11,12,13)
    s.add(day_city[10] == cities['Lisbon'])
    s.add(day_city[11] == cities['Lisbon'])
    s.add(day_city[12] == cities['Lisbon'])
    
    # Friend in Oslo between day 13-15 (days 13,14,15)
    s.add(day_city[12] == cities['Oslo'])
    s.add(day_city[13] == cities['Oslo'])
    s.add(day_city[14] == cities['Oslo'])
    
    # 3. Flight constraints: if the city changes between day d and d+1, there must be a direct flight
    for day in range(14):
        current_city = day_city[day]
        next_city = day_city[day + 1]
        s.add(Or(current_city == next_city, And(current_city != next_city, next_city in direct_flights[current_city])))
    
    # 4. Total days per city:
    city_days = {
        'Vienna': 4,
        'Milan': 2,
        'Rome': 3,
        'Riga': 2,
        'Lisbon': 3,
        'Vilnius': 4,
        'Oslo': 3
    }
    
    for city, total in city_days.items():
        city_code = cities[city]
        # Sum the days where the city is visited.
        total_days = Sum([If(day_city[day] == city_code, 1, 0) for day in range(15)])
        s.add(total_days == total)
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(15):
            current_day = day + 1
            city_code = m.evaluate(day_city[day]).as_long()
            itinerary.append({'day': current_day, 'place': city_names[city_code]})
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))