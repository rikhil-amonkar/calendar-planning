from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Stuttgart': 0,
        'Istanbul': 1,
        'Vilnius': 2,
        'Seville': 3,
        'Geneva': 4,
        'Valencia': 5,
        'Munich': 6,
        'Reykjavik': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 5, 7],  # Stuttgart
        1: [0, 2, 4, 5, 6],  # Istanbul
        2: [1, 6],  # Vilnius
        3: [5, 6],  # Seville
        4: [1, 5, 6],  # Geneva
        5: [0, 1, 3, 4, 6],  # Valencia
        6: [1, 3, 4, 5, 7],  # Munich
        7: [0, 6]  # Reykjavik
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Stuttgart
        1: 4,  # Istanbul
        2: 4,  # Vilnius
        3: 3,  # Seville
        4: 5,  # Geneva
        5: 5,  # Valencia
        6: 3,  # Munich
        7: 4   # Reykjavik
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(25)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Conference in Stuttgart (days 4-7)
    for i in range(3, 7):
        s.add(days[i] == 0)
    
    # Visit relatives in Istanbul (days 19-22)
    for i in range(18, 22):
        s.add(days[i] == 1)
    
    # Annual show in Munich (days 13-15)
    for i in range(12, 15):
        s.add(days[i] == 6)
    
    # Workshop in Reykjavik (days 1-4)
    for i in range(4):
        s.add(days[i] == 7)
    
    # Flight constraints between consecutive days
    for i in range(24):
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
        for i in range(25):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()