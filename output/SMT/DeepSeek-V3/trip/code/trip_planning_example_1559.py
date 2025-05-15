from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Valencia': 0,
        'Oslo': 1,
        'Lyon': 2,
        'Prague': 3,
        'Paris': 4,
        'Nice': 5,
        'Seville': 6,
        'Tallinn': 7,
        'Mykonos': 8,
        'Lisbon': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [4, 6, 9, 2, 3],  # Valencia
        1: [2, 3, 4, 5, 7, 9],  # Oslo
        2: [0, 3, 4, 5, 9],  # Lyon
        3: [0, 1, 2, 4, 7, 9],  # Prague
        4: [0, 1, 2, 3, 5, 6, 7, 9],  # Paris
        5: [1, 2, 4, 8, 9],  # Nice
        6: [0, 4, 9],  # Seville
        7: [1, 3, 4],  # Tallinn
        8: [5],  # Mykonos
        9: [0, 1, 2, 3, 4, 5, 6]  # Lisbon
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Valencia
        1: 3,  # Oslo
        2: 4,  # Lyon
        3: 3,  # Prague
        4: 4,  # Paris
        5: 4,  # Nice
        6: 5,  # Seville
        7: 2,  # Tallinn
        8: 5,  # Mykonos
        9: 2   # Lisbon
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(25)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Meet friends in Valencia (days 3-4)
    s.add(days[2] == 0)
    s.add(days[3] == 0)
    
    # Annual show in Seville (days 5-9)
    for i in range(4, 9):
        s.add(days[i] == 6)
    
    # Meet friend in Oslo (days 13-15)
    for i in range(12, 15):
        s.add(days[i] == 1)
    
    # Wedding in Mykonos (days 21-25)
    for i in range(20, 25):
        s.add(days[i] == 8)
    
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