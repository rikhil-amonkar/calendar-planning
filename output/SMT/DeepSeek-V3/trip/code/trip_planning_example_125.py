from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Stuttgart': 0,
        'Seville': 1,
        'Manchester': 2
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [2],  # Stuttgart
        1: [2],  # Seville
        2: [0, 1]  # Manchester
    }
    
    # Required days in each city
    required_days = {
        0: 6,  # Stuttgart
        1: 7,  # Seville
        2: 4   # Manchester
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(15)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Meet friend in Stuttgart (days 1-6)
    for i in range(6):
        s.add(days[i] == 0)
    
    # Flight constraints between consecutive days
    for i in range(14):
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
        for i in range(15):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()