from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Dubrovnik': 0,
        'Split': 1,
        'Milan': 2,
        'Porto': 3,
        'Krakow': 4,
        'Munich': 5
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [5],  # Dubrovnik
        1: [2, 4, 5],  # Split
        2: [1, 3, 4, 5],  # Milan
        3: [2, 5],  # Porto
        4: [1, 2, 5],  # Krakow
        5: [0, 1, 2, 3, 4]  # Munich
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Dubrovnik
        1: 3,  # Split
        2: 3,  # Milan
        3: 4,  # Porto
        4: 2,  # Krakow
        5: 5   # Munich
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(16)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Wedding in Milan (days 11-13)
    for i in range(10, 13):
        s.add(days[i] == 2)
    
    # Meet friends in Krakow (days 8-9)
    s.add(days[7] == 4)
    s.add(days[8] == 4)
    
    # Annual show in Munich (days 4-8)
    for i in range(3, 8):
        s.add(days[i] == 5)
    
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