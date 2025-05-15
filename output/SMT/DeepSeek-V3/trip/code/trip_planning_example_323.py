from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Split': 0,
        'Oslo': 1,
        'London': 2,
        'Porto': 3
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2],  # Split
        1: [0, 2, 3],  # Oslo
        2: [0, 1],  # London
        3: [1]  # Porto
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Split
        1: 2,  # Oslo
        2: 7,  # London
        3: 5   # Porto
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(16)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Annual show in Split (days 7-11)
    for i in range(6, 11):
        s.add(days[i] == 0)
    
    # Visit relatives in London (days 1-7)
    for i in range(7):
        s.add(days[i] == 2)
    
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