from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Riga': 0,
        'Budapest': 1,
        'Paris': 2,
        'Warsaw': 3
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 3],  # Riga
        1: [0, 2, 3],  # Budapest
        2: [0, 1, 3],  # Paris
        3: [0, 1, 2]  # Warsaw
    }
    
    # Required days in each city
    required_days = {
        0: 7,  # Riga
        1: 7,  # Budapest
        2: 4,  # Paris
        3: 2   # Warsaw
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(17)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Wedding in Riga (days 11-17)
    for i in range(10, 17):
        s.add(days[i] == 0)
    
    # Annual show in Warsaw (days 1-2)
    s.add(days[0] == 3)
    s.add(days[1] == 3)
    
    # Flight constraints between consecutive days
    for i in range(16):
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
        for i in range(17):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()