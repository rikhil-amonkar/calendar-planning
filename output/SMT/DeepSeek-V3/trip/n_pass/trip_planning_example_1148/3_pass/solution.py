from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Lisbon', 'Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Stockholm', 'Split', 'Lyon']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights as a set of tuples for quick lookup
    direct_flights = {
        ('Dubrovnik', 'Stockholm'), ('Stockholm', 'Dubrovnik'),
        ('Dubrovnik', 'Copenhagen'), ('Copenhagen', 'Dubrovnik'),
        ('Lisbon', 'Copenhagen'), ('Copenhagen', 'Lisbon'),
        ('Lisbon', 'Lyon'), ('Lyon', 'Lisbon'),
        ('Lisbon', 'Stockholm'), ('Stockholm', 'Lisbon'),
        ('Lisbon', 'Prague'), ('Prague', 'Lisbon'),
        ('Copenhagen', 'Stockholm'), ('Stockholm', 'Copenhagen'),
        ('Copenhagen', 'Split'), ('Split', 'Copenhagen'),
        ('Copenhagen', 'Prague'), ('Prague', 'Copenhagen'),
        ('Copenhagen', 'Tallinn'), ('Tallinn', 'Copenhagen'),
        ('Prague', 'Stockholm'), ('Stockholm', 'Prague'),
        ('Prague', 'Lyon'), ('Lyon', 'Prague'),
        ('Prague', 'Split'), ('Split', 'Prague'),
        ('Prague', 'Tallinn'), ('Tallinn', 'Prague'),
        ('Tallinn', 'Stockholm'), ('Stockholm', 'Tallinn'),
        ('Stockholm', 'Split'), ('Split', 'Stockholm'),
        ('Split', 'Lyon'), ('Lyon', 'Split')
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
    solver.add(Sum([If(day == city_indices['Lisbon'], 1, 0) for day in days]) == 2)
    # Dubrovnik: 5 days
    solver.add(Sum([If(day == city_indices['Dubrovnik'], 1, 0) for day in days]) == 5)
    # Copenhagen: 5 days
    solver.add(Sum([If(day == city_indices['Copenhagen'], 1, 0) for day in days]) == 5)
    # Prague: 3 days
    solver.add(Sum([If(day == city_indices['Prague'], 1, 0) for day in days]) == 3)
    # Tallinn: 2 days
    solver.add(Sum([If(day == city_indices['Tallinn'], 1, 0) for day in days]) == 2)
    # Stockholm: 4 days
    solver.add(Sum([If(day == city_indices['Stockholm'], 1, 0) for day in days]) == 4)
    # Split: 3 days
    solver.add(Sum([If(day == city_indices['Split'], 1, 0) for day in days]) == 3)
    # Lyon: 2 days
    solver.add(Sum([If(day == city_indices['Lyon'], 1, 0) for day in days]) == 2)
    
    # Event constraints
    # Workshop in Lisbon between day 4 and day 5 (i.e., day 4 or 5 must be Lisbon)
    solver.add(Or(days[3] == city_indices['Lisbon'], days[4] == city_indices['Lisbon']))
    # Meet friend in Tallinn between day 1 and day 2 (day 1 or 2 must be Tallinn)
    solver.add(Or(days[0] == city_indices['Tallinn'], days[1] == city_indices['Tallinn']))
    # Wedding in Stockholm between day 13 and day 16 (i.e., one of days 13,14,15,16 must be Stockholm)
    solver.add(Or([days[i] == city_indices['Stockholm'] for i in range(12, 16)]))
    # Annual show in Lyon from day 18 to 19 (both days must be Lyon)
    solver.add(days[17] == city_indices['Lyon'])
    solver.add(days[18] == city_indices['Lyon'])
    
    # Flight constraints: consecutive days in different cities must have a direct flight
    for i in range(len(days) - 1):
        current_city = days[i]
        next_city = days[i+1]
        # If current_city != next_city, then there must be a direct flight
        solver.add(Implies(current_city != next_city, 
                          Or([And(current_city == city_indices[a], next_city == city_indices[b]) 
                              for (a, b) in direct_flights if a != b])))
    
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