import json
from z3 import *

def main():
    # Cities and their required days
    cities = ['London', 'Zurich', 'Bucharest', 'Hamburg', 'Barcelona', 'Reykjavik', 'Stuttgart', 'Stockholm', 'Tallinn', 'Milan']
    required_days = {
        'London': 3,
        'Zurich': 2,
        'Bucharest': 2,
        'Hamburg': 5,
        'Barcelona': 4,
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Stockholm': 2,
        'Tallinn': 4,
        'Milan': 5
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ('London', 'Hamburg'),
        ('London', 'Reykjavik'),
        ('Milan', 'Barcelona'),
        ('Reykjavik', 'Barcelona'),
        ('Reykjavik', 'Stuttgart'),
        ('Stockholm', 'Reykjavik'),
        ('London', 'Stuttgart'),
        ('Milan', 'Zurich'),
        ('London', 'Barcelona'),
        ('Stockholm', 'Hamburg'),
        ('Zurich', 'Barcelona'),
        ('Stockholm', 'Stuttgart'),
        ('Milan', 'Hamburg'),
        ('Stockholm', 'Tallinn'),
        ('Hamburg', 'Bucharest'),
        ('London', 'Bucharest'),
        ('Milan', 'Stockholm'),
        ('Stuttgart', 'Hamburg'),
        ('London', 'Zurich'),
        ('Milan', 'Reykjavik'),
        ('London', 'Stockholm'),
        ('Milan', 'Stuttgart'),
        ('Stockholm', 'Barcelona'),
        ('London', 'Milan'),
        ('Zurich', 'Hamburg'),
        ('Bucharest', 'Barcelona'),
        ('Zurich', 'Stockholm'),
        ('Barcelona', 'Tallinn'),
        ('Zurich', 'Tallinn'),
        ('Hamburg', 'Barcelona'),
        ('Stuttgart', 'Barcelona'),
        ('Zurich', 'Reykjavik'),
        ('Zurich', 'Bucharest')
    ]
    
    # Create a set of direct flights for easy lookup
    flight_set = set()
    for (a, b) in direct_flights:
        flight_set.add((a, b))
        flight_set.add((b, a))
    
    # Create solver
    solver = Solver()
    
    # Create a 2D array of variables: in_city[day][city]
    # Days are from 1 to 28
    in_city = {}
    for day in range(1, 29):
        in_city[day] = {}
        for city in cities:
            in_city[day][city] = Bool(f'in_{day}_{city}')
    
    # Constraint: For each day, at least one city and at most two cities
    for day in range(1, 29):
        cities_in_day = [in_city[day][c] for c in cities]
        solver.add(AtLeast(*cities_in_day, 1))
        solver.add(AtMost(*cities_in_day, 2))
    
    # Constraint: For each city, total days equals required days
    for city in cities:
        total = 0
        for day in range(1, 29):
            total += If(in_city[day][city], 1, 0)
        solver.add(total == required_days[city])
    
    # Constraint: For each day i and city c, if in_city[i+1][c] is true, then there exists a city d in cities such that in_city[i][d] is true and (d == c or (d, c) in flight_set)
    for day in range(1, 28):
        for city in cities:
            next_day_in_c = in_city[day+1][city]
            allowed_prev = []
            for other_city in cities:
                if other_city == city:
                    allowed_prev.append(in_city[day][other_city])
                else:
                    if (other_city, city) in flight_set:
                        allowed_prev.append(in_city[day][other_city])
            solver.add(Implies(next_day_in_c, Or(allowed_prev)))
    
    # Specific constraints
    # London: days 1-3
    for day in [1,2,3]:
        solver.add(in_city[day]['London'])
    # Milan: days 3-7
    for day in [3,4,5,6,7]:
        solver.add(in_city[day]['Milan'])
    # Zurich: days 7-8
    for day in [7,8]:
        solver.add(in_city[day]['Zurich'])
    # Reykjavik: days 9-13
    for day in [9,10,11,12,13]:
        solver.add(in_city[day]['Reykjavik'])
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        # For each day, get the set of cities we are in
        day_assignments = {}
        for day in range(1, 29):
            cities_in_day = []
            for city in cities:
                if is_true(model.eval(in_city[day][city])):
                    cities_in_day.append(city)
            day_assignments[day] = sorted(cities_in_day)  # sort for consistency
        
        # Group consecutive days with the same set of cities
        itinerary = []
        start_day = 1
        current_set = day_assignments[1]
        for day in range(2, 29):
            if day_assignments[day] == current_set:
                continue
            else:
                end_day = day - 1
                if start_day == end_day:
                    day_range_str = f"Day {start_day}"
                else:
                    day_range_str = f"Day {start_day}-{end_day}"
                place_str = ", ".join(current_set)
                itinerary.append({"day_range": day_range_str, "place": place_str})
                start_day = day
                current_set = day_assignments[day]
        # Add the last group
        end_day = 28
        if start_day == end_day:
            day_range_str = f"Day {start_day}"
        else:
            day_range_str = f"Day {start_day}-{end_day}"
        place_str = ", ".join(current_set)
        itinerary.append({"day_range": day_range_str, "place": place_str})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()