from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Paris': 0,
        'Florence': 1,
        'Vienna': 2,
        'Porto': 3,
        'Munich': 4,
        'Nice': 5,
        'Warsaw': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 4, 5, 6],  # Paris
        1: [0, 2, 4],  # Florence
        2: [0, 1, 3, 4, 5, 6],  # Vienna
        3: [0, 2, 4, 5, 6],  # Porto
        4: [0, 1, 2, 3, 5, 6],  # Munich
        5: [0, 2, 3, 4, 6],  # Nice
        6: [0, 2, 3, 4, 5]  # Warsaw
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Paris
        1: 3,  # Florence
        2: 2,  # Vienna
        3: 3,  # Porto
        4: 5,  # Munich
        5: 5,  # Nice
        6: 3   # Warsaw
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(20)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Workshop in Porto (days 1-3)
    for i in range(3):
        s.add(days[i] == 3)
    
    # Wedding in Warsaw (days 13-15)
    for i in range(12, 15):
        s.add(days[i] == 6)
    
    # Visit relatives in Vienna (days 19-20)
    s.add(days[18] == 2)
    s.add(days[19] == 2)
    
    # Flight constraints between consecutive days
    for i in range(19):
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
        for i in range(20):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()