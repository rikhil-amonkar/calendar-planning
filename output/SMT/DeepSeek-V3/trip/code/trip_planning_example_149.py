from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'London': 0,
        'Santorini': 1,
        'Istanbul': 2
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2],  # London
        1: [0],  # Santorini
        2: [0]  # Istanbul
    }
    
    # Required days in each city
    required_days = {
        0: 3,  # London
        1: 6,  # Santorini
        2: 3   # Istanbul
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(10)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Conference in Santorini (days 5 and 10)
    s.add(days[4] == 1)
    s.add(days[9] == 1)
    
    # Flight constraints between consecutive days
    for i in range(9):
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
        for i in range(10):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()