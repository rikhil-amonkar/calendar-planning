from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Riga': 0,
        'Amsterdam': 1,
        'Mykonos': 2
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1],  # Riga
        1: [0, 2],  # Amsterdam
        2: [1]  # Mykonos
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Riga
        1: 2,  # Amsterdam
        2: 5   # Mykonos
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(7)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Visit relatives in Riga (days 1-2)
    s.add(days[0] == 0)
    s.add(days[1] == 0)
    
    # Flight constraints between consecutive days
    for i in range(6):
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
        for i in range(7):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()