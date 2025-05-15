from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Porto': 0,
        'Prague': 1,
        'Reykjavik': 2,
        'Santorini': 3,
        'Amsterdam': 4,
        'Munich': 5
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [4, 5],  # Porto
        1: [2, 4, 5],  # Prague
        2: [1, 4, 5],  # Reykjavik
        3: [4],  # Santorini
        4: [0, 1, 2, 3, 5],  # Amsterdam
        5: [0, 1, 2, 4]  # Munich
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Porto
        1: 4,  # Prague
        2: 4,  # Reykjavik
        3: 2,  # Santorini
        4: 2,  # Amsterdam
        5: 4   # Munich
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(16)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Wedding in Reykjavik (days 4-7)
    for i in range(3, 7):
        s.add(days[i] == 2)
    
    # Conference in Amsterdam (days 14-15)
    s.add(days[13] == 4)
    s.add(days[14] == 4)
    
    # Meet friend in Munich (days 7-10)
    for i in range(6, 10):
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