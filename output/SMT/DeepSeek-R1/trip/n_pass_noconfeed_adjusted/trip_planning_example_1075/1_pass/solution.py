import z3
import json

def main():
    # Define cities and required days
    cities = ['Reykjavik', 'Stuttgart', 'Vienna', 'Edinburgh', 'Manchester', 'Split', 'Lyon', 'Prague']
    required_days = {
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Vienna': 4,
        'Edinburgh': 4,
        'Manchester': 2,
        'Split': 5,
        'Lyon': 3,
        'Prague': 4
    }
    
    # Build undirected flight graph from given connections
    connections = [
        ('Reykjavik', 'Stuttgart'),
        ('Stuttgart', 'Split'),
        ('Stuttgart', 'Vienna'),
        ('Prague', 'Manchester'),
        ('Edinburgh', 'Prague'),
        ('Manchester', 'Split'),
        ('Prague', 'Vienna'),
        ('Vienna', 'Manchester'),
        ('Prague', 'Split'),
        ('Vienna', 'Lyon'),
        ('Stuttgart', 'Edinburgh'),
        ('Split', 'Lyon'),
        ('Stuttgart', 'Manchester'),
        ('Prague', 'Lyon'),
        ('Reykjavik', 'Vienna'),
        ('Prague', 'Reykjavik'),
        ('Vienna', 'Split')
    ]
    
    edges = set()
    for conn in connections:
        u, v = conn
        if u > v:
            u, v = v, u
        edges.add((u, v))
    
    # Create Z3 solver and variables
    num_days = 25
    in_city = [[z3.Bool(f'in_day{day+1}_{city}') for city in cities] for day in range(num_days)]
    solver = z3.Solver()
    
    # Constraint: Each day must have at least one city and at most two cities
    for day in range(num_days):
        solver.add(z3.Or(
            z3.Sum([z3.If(in_city[day][i], 1, 0) for i in range(len(cities))]) == 1,
            z3.Sum([z3.If(in_city[day][i], 1, 0) for i in range(len(cities))]) == 2
        ))
    
    # Constraint: First and last days must have exactly one city
    solver.add(z3.Sum([z3.If(in_city[0][i], 1, 0) for i in range(len(cities))]) == 1)
    solver.add(z3.Sum([z3.If(in_city[24][i], 1, 0) for i in range(len(cities))]) == 1)
    
    # Constraint: Total days per city must match requirements
    for c_idx, city in enumerate(cities):
        total = required_days[city]
        solver.add(z3.Sum([z3.If(in_city[d][c_idx], 1, 0) for d in range(num_days)]) == total)
    
    # Constraint: Edinburgh from day 5 to day 8 (indices 4 to 7)
    edinburgh_idx = cities.index('Edinburgh')
    for d in [4,5,6,7]:
        solver.add(in_city[d][edinburgh_idx] == True)
    
    # Constraint: Split between day 19 and day 23 (indices 18 to 22)
    split_idx = cities.index('Split')
    solver.add(z3.Or([in_city[d][split_idx] for d in range(18, 23)]))
    
    # Constraint: Presence change implies travel day
    for c_idx in range(len(cities)):
        for d in range(num_days-1):
            solver.add(z3.Implies(
                in_city[d][c_idx] != in_city[d+1][c_idx],
                z3.Sum([z3.If(in_city[d][i], 1, 0) for i in range(len(cities))]) == 2
            ))
    
    # Constraint: Connected cities for travel days
    for d in range(num_days):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                city1 = cities[i]
                city2 = cities[j]
                key = (city1, city2) if city1 < city2 else (city2, city1)
                if key not in edges:
                    solver.add(z3.Not(z3.And(in_city[d][i], in_city[d][j])))
    
    # Solve and output
    if solver.check() == z3.sat:
        model = solver.model()
        days_per_city = {city: [] for city in cities}
        
        for d in range(num_days):
            for c_idx, city in enumerate(cities):
                if z3.is_true(model.evaluate(in_city[d][c_idx])):
                    days_per_city[city].append(d+1)
        
        itinerary = []
        for city, days in days_per_city.items():
            days.sort()
            start = days[0]
            current = start
            for i in range(1, len(days)):
                if days[i] != days[i-1] + 1:
                    itinerary.append((start, current, city))
                    start = days[i]
                current = days[i]
            itinerary.append((start, current, city))
        
        itinerary.sort(key=lambda x: x[0])
        result = []
        for start, end, city in itinerary:
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            result.append({"day_range": day_range, "place": city})
        
        print(json.dumps({"itinerary": result}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()