import json
from z3 import *

def main():
    # Define cities and their required days
    city_names = ['Venice', 'Reykjavik', 'Munich', 'Santorini', 'Manchester', 'Porto', 'Bucharest', 'Tallinn', 'Valencia', 'Vienna']
    required_days = [3, 2, 3, 3, 3, 3, 5, 4, 2, 5]
    
    # Direct flights list
    direct_flights = [
        ('Bucharest', 'Manchester'),
        ('Munich', 'Venice'),
        ('Santorini', 'Manchester'),
        ('Vienna', 'Reykjavik'),
        ('Venice', 'Santorini'),
        ('Munich', 'Porto'),
        ('Valencia', 'Vienna'),
        ('Manchester', 'Vienna'),
        ('Porto', 'Vienna'),
        ('Venice', 'Manchester'),
        ('Santorini', 'Vienna'),
        ('Munich', 'Manchester'),
        ('Munich', 'Reykjavik'),
        ('Bucharest', 'Valencia'),
        ('Venice', 'Vienna'),
        ('Bucharest', 'Vienna'),
        ('Porto', 'Manchester'),
        ('Munich', 'Vienna'),
        ('Valencia', 'Porto'),
        ('Munich', 'Bucharest'),
        ('Tallinn', 'Munich'),
        ('Santorini', 'Bucharest'),
        ('Munich', 'Valencia')
    ]
    
    # Create city index mapping
    city_index = {city: idx for idx, city in enumerate(city_names)}
    
    # Build connected matrix (10x10)
    connected = [[False] * 10 for _ in range(10)]
    for (a, b) in direct_flights:
        i = city_index[a]
        j = city_index[b]
        connected[i][j] = True
        connected[j][i] = True
    
    # Initialize Z3 solver
    solver = Solver()
    
    # Create present matrix (24 days x 10 cities)
    present = [[Bool(f"d{i}c{c}") for c in range(10)] for i in range(24)]
    
    # Constraint 1: Each day has exactly 1 or 2 cities
    for i in range(24):
        solver.add(Or(Sum([If(present[i][c], 1, 0) for c in range(10)]) == 1,
                     Sum([If(present[i][c], 1, 0) for c in range(10)]) == 2))
    
    # Constraint 2: Total city-days must be 33
    total_city_days = Sum([If(present[i][c], 1, 0) for i in range(24) for c in range(10)])
    solver.add(total_city_days == 33)
    
    # Constraint 3: Required days per city
    for c in range(10):
        solver.add(Sum([If(present[i][c], 1, 0) for i in range(24)]) == required_days[c])
    
    # Constraint 4: Specific day constraints
    munich_idx = city_index['Munich']
    santorini_idx = city_index['Santorini']
    valencia_idx = city_index['Valencia']
    
    # Munich on days 4,5,6 (index 3,4,5)
    solver.add(present[3][munich_idx] == True)
    solver.add(present[4][munich_idx] == True)
    solver.add(present[5][munich_idx] == True)
    
    # Santorini on days 8,9,10 (index 7,8,9)
    solver.add(present[7][santorini_idx] == True)
    solver.add(present[8][santorini_idx] == True)
    solver.add(present[9][santorini_idx] == True)
    
    # Valencia on days 14,15 (index 13,14)
    solver.add(present[13][valencia_idx] == True)
    solver.add(present[14][valencia_idx] == True)
    
    # Constraint 5: If two cities on same day, must have direct flight
    for i in range(24):
        for c1 in range(10):
            for c2 in range(c1+1, 10):
                solver.add(Implies(And(present[i][c1], present[i][c2]), connected[c1][c2]))
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        day_assignments = []
        for i in range(24):
            cities_today = []
            for c in range(10):
                if is_true(model.evaluate(present[i][c])):
                    cities_today.append(city_names[c])
            day_assignments.append(cities_today)
        
        # Build list of days per city
        city_days = {city: [] for city in city_names}
        for day_idx, cities in enumerate(day_assignments):
            for city in cities:
                city_days[city].append(day_idx + 1)  # 1-indexed days
        
        # Group consecutive days for each city
        itinerary_list = []
        for city, days_list in city_days.items():
            if not days_list:
                continue
            days_list.sort()
            start = days_list[0]
            prev = days_list[0]
            for day in days_list[1:]:
                if day == prev + 1:
                    prev = day
                else:
                    if start == prev:
                        day_range_str = f"Day {start}"
                    else:
                        day_range_str = f"Day {start}-{prev}"
                    itinerary_list.append({"day_range": day_range_str, "place": city})
                    start = day
                    prev = day
            if start == prev:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{prev}"
            itinerary_list.append({"day_range": day_range_str, "place": city})
        
        # Sort itinerary by start day
        def get_start_day(entry):
            s = entry['day_range'].replace('Day ', '')
            if '-' in s:
                return int(s.split('-')[0])
            return int(s)
        
        itinerary_list.sort(key=get_start_day)
        
        # Output as JSON
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')
        return

if __name__ == '__main__':
    main()