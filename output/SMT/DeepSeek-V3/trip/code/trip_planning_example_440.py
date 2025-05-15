from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Split': 0,
        'Helsinki': 1,
        'Reykjavik': 2,
        'Vilnius': 3,
        'Geneva': 4
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 3, 4],  # Split
        1: [0, 2, 3, 4],  # Helsinki
        2: [1],  # Reykjavik
        3: [0, 1],  # Vilnius
        4: [0, 1]  # Geneva
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Split
        1: 2,  # Helsinki
        2: 3,  # Reykjavik
        3: 3,  # Vilnius
        4: 6   # Geneva
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(12)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Wedding in Reykjavik (days 10-12)
    for i in range(9, 12):
        s.add(days[i] == 2)
    
    # Visit relatives in Vilnius (days 7-9)
    for i in range(6, 9):
        s.add(days[i] == 3)
    
    # Flight constraints between consecutive days
    for i in range(11):
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
        for i in range(12):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()