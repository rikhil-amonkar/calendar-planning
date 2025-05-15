from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Mykonos': 0,
        'Riga': 1,
        'Munich': 2,
        'Bucharest': 3,
        'Rome': 4,
        'Nice': 5,
        'Krakow': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [2, 4, 5],  # Mykonos
        1: [2, 3, 5],  # Riga
        2: [0, 1, 3, 4, 5, 6],  # Munich
        3: [1, 2, 4],  # Bucharest
        4: [0, 2, 3, 5],  # Rome
        5: [0, 1, 2, 4],  # Nice
        6: [2]  # Krakow
    }
    
    # Required days in each city
    required_days = {
        0: 3,  # Mykonos
        1: 3,  # Riga
        2: 4,  # Munich
        3: 4,  # Bucharest
        4: 4,  # Rome
        5: 3,  # Nice
        6: 2   # Krakow
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(17)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Wedding in Mykonos (days 4-6)
    for i in range(3, 6):
        s.add(days[i] == 0)
    
    # Conference in Rome (days 1-4)
    for i in range(4):
        s.add(days[i] == 4)
    
    # Annual show in Krakow (days 16-17)
    s.add(days[15] == 6)
    s.add(days[16] == 6)
    
    # Flight constraints between consecutive days
    for i in range(16):
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
        for i in range(17):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()