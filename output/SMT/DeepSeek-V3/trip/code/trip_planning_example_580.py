from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Paris': 0,
        'Oslo': 1,
        'Porto': 2,
        'Geneva': 3,
        'Reykjavik': 4
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 3, 4],  # Paris
        1: [0, 2, 3, 4],  # Oslo
        2: [0, 1, 3],  # Porto
        3: [0, 1, 2],  # Geneva
        4: [0, 1]  # Reykjavik
    }
    
    # Required days in each city
    required_days = {
        0: 6,  # Paris
        1: 5,  # Oslo
        2: 7,  # Porto
        3: 7,  # Geneva
        4: 2   # Reykjavik
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(23)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Conference in Geneva (days 1-7)
    for i in range(7):
        s.add(days[i] == 3)
    
    # Visit relatives in Oslo (days 19-23)
    for i in range(18, 23):
        s.add(days[i] == 1)
    
    # Flight constraints between consecutive days
    for i in range(22):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(next_day == current, 
               And(next_day != current, 
                   Or([next_day == dest for dest in direct_flights[current]])))
    
    # Total days in each city must match requirements
    for city in cities.values():
        total = Sum([If(day == city, 1, 0) for day in days])
        s.add(total == required_days[city])
    
    # Solve and print schedule
    if s.check() == sat:
        m = s.model()
        schedule = [m[day].as_long() for day in days]
        print("Day\tCity")
        for i in range(23):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()