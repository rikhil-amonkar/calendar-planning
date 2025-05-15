from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Prague': 0,
        'Stuttgart': 1,
        'Split': 2,
        'Krakow': 3,
        'Florence': 4
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 3, 4],  # Prague
        1: [0, 2, 3],  # Stuttgart
        2: [0, 1, 3],  # Split
        3: [0, 1, 2],  # Krakow
        4: [0]  # Florence
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Prague
        1: 2,  # Stuttgart
        2: 2,  # Split
        3: 2,  # Krakow
        4: 2   # Florence
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(8)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Wedding in Stuttgart (days 2-3)
    s.add(days[1] == 1)
    s.add(days[2] == 1)
    
    # Meet friends in Split (days 3-4)
    s.add(days[2] == 2)
    s.add(days[3] == 2)
    
    # Flight constraints between consecutive days
    for i in range(7):
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
        for i in range(8):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()