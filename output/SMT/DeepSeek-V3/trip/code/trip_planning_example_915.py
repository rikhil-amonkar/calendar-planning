from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Bucharest': 0,
        'Venice': 1,
        'Prague': 2,
        'Frankfurt': 3,
        'Zurich': 4,
        'Florence': 5,
        'Tallinn': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 3, 4],  # Bucharest
        1: [0, 3, 4],  # Venice
        2: [0, 3, 4, 5, 6],  # Prague
        3: [0, 1, 2, 4, 5, 6],  # Frankfurt
        4: [0, 1, 2, 3, 5, 6],  # Zurich
        5: [2, 3, 4],  # Florence
        6: [2, 3, 4]  # Tallinn
    }
    
    # Required days in each city
    required_days = {
        0: 3,  # Bucharest
        1: 5,  # Venice
        2: 4,  # Prague
        3: 5,  # Frankfurt
        4: 5,  # Zurich
        5: 5,  # Florence
        6: 5   # Tallinn
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(26)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Wedding in Venice (days 22-26)
    for i in range(21, 26):
        s.add(days[i] == 1)
    
    # Annual show in Frankfurt (days 12-16)
    for i in range(11, 16):
        s.add(days[i] == 3)
    
    # Meet friends in Tallinn (days 8-12)
    for i in range(7, 12):
        s.add(days[i] == 6)
    
    # Flight constraints between consecutive days
    for i in range(25):
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
        for i in range(26):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()