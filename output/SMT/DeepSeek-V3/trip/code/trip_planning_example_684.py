from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Amsterdam': 0,
        'Edinburgh': 1,
        'Brussels': 2,
        'Vienna': 3,
        'Berlin': 4,
        'Reykjavik': 5
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 3, 4, 5],  # Amsterdam
        1: [0, 2, 4],  # Edinburgh
        2: [1, 3, 4, 5],  # Brussels
        3: [0, 2, 4, 5],  # Vienna
        4: [0, 1, 2, 3, 5],  # Berlin
        5: [0, 2, 3, 4]  # Reykjavik
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Amsterdam
        1: 5,  # Edinburgh
        2: 5,  # Brussels
        3: 5,  # Vienna
        4: 4,  # Berlin
        5: 5   # Reykjavik
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..23)
    days = [Int(f'day_{i}') for i in range(23)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 6 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: visit relatives in Amsterdam between days 5-8 (days 4-7 in 0-based)
    for i in range(4, 8):
        s.add(days[i] == 0)
    
    # Constraint: meet friend in Berlin between days 16-19 (days 15-18 in 0-based)
    for i in range(15, 19):
        s.add(days[i] == 4)
    
    # Constraint: workshop in Reykjavik between days 12-16 (days 11-15 in 0-based)
    for i in range(11, 16):
        s.add(days[i] == 5)
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(22):
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
        for i in range(23):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()