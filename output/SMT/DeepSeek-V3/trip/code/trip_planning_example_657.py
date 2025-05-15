from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Frankfurt': 0,
        'Manchester': 1,
        'Valencia': 2,
        'Naples': 3,
        'Oslo': 4,
        'Vilnius': 5
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 3, 4, 5],  # Frankfurt
        1: [0, 3, 4],  # Manchester
        2: [0, 3],  # Valencia
        3: [0, 1, 2, 4],  # Naples
        4: [0, 1, 3, 5],  # Oslo
        5: [0, 4]  # Vilnius
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Frankfurt
        1: 4,  # Manchester
        2: 4,  # Valencia
        3: 4,  # Naples
        4: 3,  # Oslo
        5: 2   # Vilnius
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(16)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Annual show in Frankfurt (days 13-16)
    for i in range(12, 16):
        s.add(days[i] == 0)
    
    # Wedding in Vilnius (days 12-13)
    s.add(days[11] == 5)
    s.add(days[12] == 5)
    
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