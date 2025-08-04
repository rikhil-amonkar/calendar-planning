from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Lisbon', 'Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Stockholm', 'Split', 'Lyon']
    
    # Direct flights as a dictionary for quick lookup
    direct_flights = {
        'Dubrovnik': ['Stockholm', 'Copenhagen'],
        'Lisbon': ['Copenhagen', 'Lyon', 'Stockholm', 'Prague'],
        'Copenhagen': ['Lisbon', 'Stockholm', 'Split', 'Dubrovnik', 'Prague', 'Tallinn'],
        'Prague': ['Stockholm', 'Lyon', 'Lisbon', 'Copenhagen', 'Split', 'Tallinn'],
        'Tallinn': ['Stockholm', 'Copenhagen', 'Prague'],
        'Stockholm': ['Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Lisbon', 'Split'],
        'Split': ['Copenhagen', 'Stockholm', 'Prague', 'Lyon'],
        'Lyon': ['Lisbon', 'Prague', 'Split']
    }
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Variables: day_1 to day_19, each can be one of the cities
    days = [Int(f'day_{i}') for i in range(1, 20)]  # days 1..19
    
    # Each day variable must be between 0 and 7 (representing the index in cities)
    for day in days:
        solver.add(day >= 0, day < len(cities))
    
    # Duration constraints
    # Lisbon: 2 days
    solver.add(Sum([If(day == cities.index('Lisbon'), 1, 0) for day in days]) == 2)
    # Dubrovnik: 5 days
    solver.add(Sum([If(day == cities.index('Dubrovnik'), 1, 0) for day in days]) == 5)
    # Copenhagen: 5 days
    solver.add(Sum([If(day == cities.index('Copenhagen'), 1, 0) for day in days]) == 5)
    # Prague: 3 days
    solver.add(Sum([If(day == cities.index('Prague'), 1, 0) for day in days]) == 3)
    # Tallinn: 2 days
    solver.add(Sum([If(day == cities.index('Tallinn'), 1, 0) for day in days]) == 2)
    # Stockholm: 4 days
    solver.add(Sum([If(day == cities.index('Stockholm'), 1, 0) for day in days]) == 4)
    # Split: 3 days
    solver.add(Sum([If(day == cities.index('Split'), 1, 0) for day in days]) == 3)
    # Lyon: 2 days
    solver.add(Sum([If(day == cities.index('Lyon'), 1, 0) for day in days]) == 2)
    
    # Event constraints
    # Workshop in Lisbon between day 4 and day 5 (i.e., day 4 or 5 must be Lisbon)
    solver.add(Or(days[3] == cities.index('Lisbon'), days[4] == cities.index('Lisbon')))
    # Meet friend in Tallinn between day 1 and day 2 (day 1 or 2 must be Tallinn)
    solver.add(Or(days[0] == cities.index('Tallinn'), days[1] == cities.index('Tallinn')))
    # Wedding in Stockholm between day 13 and day 16 (i.e., one of days 13,14,15,16 must be Stockholm)
    solver.add(Or([days[i] == cities.index('Stockholm') for i in range(12, 16)]))
    # Annual show in Lyon from day 18 to 19 (both days must be Lyon)
    solver.add(days[17] == cities.index('Lyon'))
    solver.add(days[18] == cities.index('Lyon'))
    
    # Flight constraints: consecutive days in different cities must have a direct flight
    for i in range(len(days) - 1):
        current_city = days[i]
        next_city = days[i+1]
        # If current_city != next_city, then there must be a direct flight
        solver.add(Implies(current_city != next_city, 
                          Or([And(current_city == cities.index(a), next_city == cities.index(b)) 
                              for a in direct_flights for b in direct_flights[a] if a != b])))
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(1, 20):
            day_var = days[i-1]
            city_index = model[day_var].as_long()
            itinerary.append({'day': i, 'place': cities[city_index]})
        
        # Verify the solution meets all constraints
        # (This is handled by Z3, but for thoroughness, we could add checks here)
        
        # Format the output as required
        output = {'itinerary': itinerary}
        return output
    else:
        return None

# Solve and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print("No solution found.")