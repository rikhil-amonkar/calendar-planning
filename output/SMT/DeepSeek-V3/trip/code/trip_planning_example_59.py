from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Lyon': 0,
        'Bucharest': 1,
        'Porto': 2
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2],  # Lyon
        1: [0],  # Bucharest
        2: [0]  # Porto
    }
    
    # Required days in each city
    required_days = {
        0: 7,  # Lyon
        1: 7,  # Bucharest
        2: 4   # Porto
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(16)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Wedding in Bucharest (days 1-7)
    for i in range(7):
        s.add(days[i] == 1)
    
    # Flight constraints between consecutive days
    for i in range(15):
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
        for i in range(16):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()