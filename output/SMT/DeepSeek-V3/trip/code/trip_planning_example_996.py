from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Valencia': 0,
        'Riga': 1,
        'Prague': 2,
        'Mykonos': 3,
        'Zurich': 4,
        'Bucharest': 5,
        'Nice': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [4, 5],  # Valencia
        1: [2, 4, 5, 6],  # Riga
        2: [1, 4, 5, 0],  # Prague
        3: [4, 6],  # Mykonos
        4: [0, 1, 2, 3, 5, 6],  # Zurich
        5: [0, 1, 2, 4],  # Bucharest
        6: [1, 3, 4]  # Nice
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Valencia
        1: 5,  # Riga
        2: 3,  # Prague
        3: 3,  # Mykonos
        4: 5,  # Zurich
        5: 5,  # Bucharest
        6: 2   # Nice
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(22)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Wedding in Mykonos (days 1-3)
    for i in range(3):
        s.add(days[i] == 3)
    
    # Visit relatives in Prague (days 7-9)
    for i in range(6, 9):
        s.add(days[i] == 2)
    
    # Flight constraints between consecutive days
    for i in range(21):
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
        for i in range(22):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()