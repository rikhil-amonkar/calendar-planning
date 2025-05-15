from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Oslo': 0,
        'Helsinki': 1,
        'Edinburgh': 2,
        'Riga': 3,
        'Tallinn': 4,
        'Budapest': 5,
        'Vilnius': 6,
        'Porto': 7,
        'Geneva': 8
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 3, 4, 5, 6, 7, 8],  # Oslo
        1: [0, 2, 3, 4, 5, 6, 8],  # Helsinki
        2: [0, 1, 3, 5, 7, 8],  # Edinburgh
        3: [0, 1, 2, 4, 6],  # Riga
        4: [0, 1, 3, 6],  # Tallinn
        5: [0, 1, 2, 8],  # Budapest
        6: [0, 1, 3, 4],  # Vilnius
        7: [0, 2, 8],  # Porto
        8: [0, 1, 2, 5, 7]  # Geneva
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Oslo
        1: 2,  # Helsinki
        2: 3,  # Edinburgh
        3: 2,  # Riga
        4: 5,  # Tallinn
        5: 5,  # Budapest
        6: 5,  # Vilnius
        7: 5,  # Porto
        8: 4   # Geneva
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(25)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Meet friend in Oslo (days 24-25)
    s.add(days[23] == 0)
    s.add(days[24] == 0)
    
    # Wedding in Tallinn (days 4-8)
    for i in range(3, 8):
        s.add(days[i] == 4)
    
    # Flight constraints between consecutive days
    for i in range(24):
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
        for i in range(25):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()