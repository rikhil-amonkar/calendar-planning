from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Riga': 0,
        'Manchester': 1,
        'Bucharest': 2,
        'Florence': 3,
        'Vienna': 4,
        'Istanbul': 5,
        'Reykjavik': 6,
        'Stuttgart': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 4, 5],  # Riga
        1: [0, 2, 4, 5, 7],  # Manchester
        2: [0, 1, 4, 5],  # Bucharest
        3: [4],  # Florence
        4: [0, 1, 2, 3, 5, 6, 7],  # Vienna
        5: [0, 1, 2, 4, 7],  # Istanbul
        6: [4, 7],  # Reykjavik
        7: [1, 4, 5, 6]  # Stuttgart
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Riga
        1: 5,  # Manchester
        2: 4,  # Bucharest
        3: 4,  # Florence
        4: 2,  # Vienna
        5: 2,  # Istanbul
        6: 4,  # Reykjavik
        7: 5   # Stuttgart
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(23)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Workshop in Bucharest (days 16-19)
    for i in range(15, 19):
        s.add(days[i] == 2)
    
    # Annual show in Istanbul (days 12-13)
    s.add(days[11] == 5)
    s.add(days[12] == 5)
    
    # Flight constraints between consecutive days
    for i in range(22):
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
        for i in range(23):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()