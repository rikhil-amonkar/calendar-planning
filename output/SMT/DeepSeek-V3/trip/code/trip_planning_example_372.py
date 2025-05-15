from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Seville': 0,
        'Stuttgart': 1,
        'Porto': 2,
        'Madrid': 3
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [2, 3],  # Seville
        1: [2],     # Stuttgart
        2: [0, 1, 3],  # Porto
        3: [0, 2]   # Madrid
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Seville
        1: 7,  # Stuttgart
        2: 3,  # Porto
        3: 4   # Madrid
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(13)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Visit relatives in Madrid (days 1-4)
    for i in range(4):
        s.add(days[i] == 3)
    
    # Conference in Stuttgart (days 7-13)
    for i in range(6, 13):
        s.add(days[i] == 1)
    
    # Flight constraints between consecutive days
    for i in range(12):
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
        for i in range(13):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()