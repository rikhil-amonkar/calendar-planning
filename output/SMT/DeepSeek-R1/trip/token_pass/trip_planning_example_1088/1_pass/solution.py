import json
from z3 import *

def main():
    # Cities and their indices
    cities = ['Reykjavik', 'Oslo', 'Stuttgart', 'Split', 'Geneva', 'Porto', 'Tallinn', 'Stockholm']
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Required days per city
    required_days = [2, 5, 5, 3, 2, 3, 5, 3]
    
    # Graph of direct flights (undirected)
    graph = [
        [1, 2, 6, 7],  # Reykjavik
        [0, 3, 4, 5, 6, 7],  # Oslo
        [0, 3, 5, 7],  # Stuttgart
        [1, 2, 4, 7],  # Split
        [1, 3, 5, 7],  # Geneva
        [1, 2, 4],  # Porto
        [0, 1],  # Tallinn
        [0, 1, 2, 3, 4]  # Stockholm
    ]
    
    # Create allowed pairs from graph
    allowed_pairs = []
    for u in range(len(cities)):
        for v in graph[u]:
            allowed_pairs.append((u, v))
    
    # Initialize Z3 variables for 21 days
    num_days = 21
    city_start = [Int(f'city_start_{i}') for i in range(num_days)]
    city_end = [Int(f'city_end_{i}') for i in range(num_days)]
    flight = [Bool(f'flight_{i}') for i in range(num_days)]
    
    solver = Solver()
    
    # Constraint: city_start for day0 is Reykjavik
    solver.add(city_start[0] == city_index['Reykjavik'])
    
    # Constraints for each day
    for i in range(num_days):
        # Domain constraints
        solver.add(city_start[i] >= 0, city_start[i] < len(cities))
        solver.add(city_end[i] >= 0, city_end[i] < len(cities))
        
        # Flight constraints
        solver.add(If(flight[i], 
                      And(city_start[i] != city_end[i], 
                          Or([And(city_start[i] == u, city_end[i] == v) for u, v in allowed_pairs])),
                      city_start[i] == city_end[i]))
        
        # Continuity constraint
        if i < num_days - 1:
            solver.add(city_start[i+1] == city_end[i])
    
    # Presence constraints
    presence = [[Bool(f'presence_{c}_{i}') for i in range(num_days)] for c in range(len(cities))]
    for c in range(len(cities)):
        for i in range(num_days):
            solver.add(presence[c][i] == Or(city_start[i] == c, And(flight[i], city_end[i] == c)))
    
    # Total days per city
    for c in range(len(cities)):
        solver.add(Sum([If(presence[c][i], 1, 0) for i in range(num_days)]) == required_days[c])
    
    # Specific constraints
    # Reykjavik on day1 and day2
    solver.add(presence[city_index['Reykjavik']][0] == True)
    solver.add(presence[city_index['Reykjavik']][1] == True)
    
    # Porto on day19,20,21
    solver.add(presence[city_index['Porto']][18] == True)
    solver.add(presence[city_index['Porto']][19] == True)
    solver.add(presence[city_index['Porto']][20] == True)
    
    # Stockholm between day2 and day4
    solver.add(Or(presence[city_index['Stockholm']][1], 
                  presence[city_index['Stockholm']][2], 
                  presence[city_index['Stockholm']][3]))
    
    # Exactly 7 flights
    solver.add(Sum([If(flight[i], 1, 0) for i in range(num_days)]) == 7)
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        # Extract the city_start for each day
        itinerary_days = []
        for i in range(num_days):
            val = model[city_start[i]]
            if val is not None:
                itinerary_days.append(val.as_long())
        
        # Group consecutive days with the same city
        itinerary = []
        start = 0
        current_city = itinerary_days[0]
        for day in range(1, num_days):
            if itinerary_days[day] != current_city:
                end = day
                itinerary.append({
                    "day_range": f"Day {start+1}-{end}",
                    "place": cities[current_city]
                })
                start = day
                current_city = itinerary_days[day]
        itinerary.append({
            "day_range": f"Day {start+1}-{num_days}",
            "place": cities[current_city]
        })
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()