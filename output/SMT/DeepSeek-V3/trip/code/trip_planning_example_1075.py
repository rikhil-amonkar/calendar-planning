from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Vienna': 0,
        'Lyon': 1,
        'Edinburgh': 2,
        'Reykjavik': 3,
        'Stuttgart': 4,
        'Manchester': 5,
        'Split': 6,
        'Prague': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 3, 4, 5, 6, 7],  # Vienna
        1: [0, 6, 7],  # Lyon
        2: [4, 7],  # Edinburgh
        3: [0, 4, 7],  # Reykjavik
        4: [0, 2, 3, 5, 6],  # Stuttgart
        5: [0, 4, 6, 7],  # Manchester
        6: [0, 1, 4, 5, 7],  # Split
        7: [0, 1, 2, 3, 5, 6]  # Prague
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Vienna
        1: 3,  # Lyon
        2: 4,  # Edinburgh
        3: 5,  # Reykjavik
        4: 5,  # Stuttgart
        5: 2,  # Manchester
        6: 5,  # Split
        7: 4   # Prague
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..25)
    days = [Int(f'day_{i}') for i in range(25)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 8 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: annual show in Edinburgh between days 5-8 (days 4-7 in 0-based)
    for i in range(4, 8):
        s.add(days[i] == 2)
    
    # Constraint: wedding in Split between days 19-23 (days 18-22 in 0-based)
    for i in range(18, 23):
        s.add(days[i] == 6)
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(24):
        current_city = days[i]
        next_city = days[i+1]
        s.add(Or(next_city == current_city, 
                 And(next_city != current_city, 
                     Or([next_city == dest for dest in direct_flights[current_city]]))))
    
    # Constraint: total days in each city must match required_days
    for city in cities.values():
        total_days = Sum([If(day == city, 1, 0) for day in days])
        s.add(total_days == required_days[city])
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        schedule = [m[day].as_long() for day in days]
        # Print the schedule
        print("Day\tCity")
        for i in range(25):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()