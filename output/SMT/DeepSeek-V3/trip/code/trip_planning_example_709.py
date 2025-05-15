from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Helsinki': 0,
        'Valencia': 1,
        'Dubrovnik': 2,
        'Porto': 3,
        'Prague': 4,
        'Reykjavik': 5
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [2, 4, 5],  # Helsinki
        1: [3, 4],  # Valencia
        2: [0],  # Dubrovnik
        3: [1],  # Porto
        4: [0, 1, 5],  # Prague
        5: [0, 4]  # Reykjavik
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Helsinki
        1: 5,  # Valencia
        2: 4,  # Dubrovnik
        3: 3,  # Porto
        4: 3,  # Prague
        5: 4   # Reykjavik
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(18)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Meet friend in Porto (days 16-18)
    for i in range(15, 18):
        s.add(days[i] == 3)
    
    # Flight constraints between consecutive days
    for i in range(17):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(next_day == current, 
               And(next_day != current, 
                   Or([next_day == dest for dest in direct_flights[current]]))))
    
    # Total days in each city must match requirements
    for city in cities.values():
        total = Sum([If(day == city, 1, 0) for day in days])
        s.add(total == required_days[city])
    
    # Solve and print schedule
    if s.check() == sat:
        m = s.model()
        schedule = [m[day].as_long() for day in days]
        print("Day\tCity")
        for i in range(18):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()