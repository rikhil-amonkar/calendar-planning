from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Reykjavik': 0,
        'Istanbul': 1,
        'Edinburgh': 2,
        'Oslo': 3,
        'Stuttgart': 4,
        'Bucharest': 5
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [3, 4],  # Reykjavik
        1: [2, 3, 4, 5],  # Istanbul
        2: [1, 3, 4],  # Edinburgh
        3: [0, 1, 2, 5],  # Oslo
        4: [0, 1, 2],  # Stuttgart
        5: [1, 3]  # Bucharest
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Reykjavik
        1: 4,  # Istanbul
        2: 5,  # Edinburgh
        3: 2,  # Oslo
        4: 3,  # Stuttgart
        5: 5   # Bucharest
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(19)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Meet friends in Istanbul (days 5-8)
    for i in range(4, 8):
        s.add(days[i] == 1)
    
    # Visit relatives in Oslo (days 8-9)
    s.add(days[7] == 3)
    s.add(days[8] == 3)
    
    # Flight constraints between consecutive days
    for i in range(18):
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
        for i in range(19):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()