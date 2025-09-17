import json
from z3 import *

def main():
    # Define the cities
    cities = ['Athens', 'Valencia', 'Zurich', 'Naples']
    city_dict = {0: 'Athens', 1: 'Valencia', 2: 'Zurich', 3: 'Naples'}
    
    # Initialize solver
    solver = Solver()
    
    # Create a 2D array of booleans: in_city[day][city]
    in_city = [[Bool(f"day_{day}_city_{city}") for city in range(4)] for day in range(1, 21)]
    
    # Constraint: For each day, at least one city and at most two cities
    for day in range(20):
        day_vars = in_city[day]
        solver.add(Or(day_vars))
        solver.add(Sum([If(var, 1, 0) for var in day_vars]) <= 2)
    
    # Total days per city
    total_days = [0]*4
    for city in range(4):
        total_days[city] = Sum([If(in_city[day][city], 1, 0) for day in range(20)])
    solver.add(total_days[0] == 6)  # Athens
    solver.add(total_days[1] == 6)  # Valencia
    solver.add(total_days[2] == 6)  # Zurich
    solver.add(total_days[3] == 5)  # Naples
    
    # Constraints for Athens: days 1-5 only Athens, day6 must include Athens
    for day in range(0, 5):  # days 1-5 (index 0 to 4)
        solver.add(in_city[day][0] == True)
        for city in [1,2,3]:
            solver.add(in_city[day][city] == False)
    solver.add(in_city[5][0] == True)  # day6 must include Athens
    
    # Constraints for Naples: days 17-20 only Naples, day16 must include Naples
    for day in range(16, 20):  # days 17-20 (index 16 to 19)
        solver.add(in_city[day][3] == True)
        for city in [0,1,2]:
            solver.add(in_city[day][city] == False)
    solver.add(in_city[15][3] == True)  # day16 must include Naples
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        # Extract the days for each city
        city_days = [[] for _ in range(4)]
        for day in range(20):
            for city in range(4):
                if is_true(model.evaluate(in_city[day][city])):
                    city_days[city].append(day+1)
        
        # Create intervals for each city
        intervals = []
        for city in range(4):
            days = city_days[city]
            if not days:
                continue
            days.sort()
            start = days[0]
            end = days[0]
            for i in range(1, len(days)):
                if days[i] == days[i-1] + 1:
                    end = days[i]
                else:
                    intervals.append((start, end, city_dict[city]))
                    start = days[i]
                    end = days[i]
            intervals.append((start, end, city_dict[city]))
        
        # Sort intervals by start day
        intervals.sort(key=lambda x: x[0])
        
        # Convert to output format
        itinerary = []
        for start, end, city in intervals:
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()