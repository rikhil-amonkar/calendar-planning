from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Venice': 0,
        'Reykjavik': 1,
        'Munich': 2,
        'Santorini': 3,
        'Manchester': 4,
        'Porto': 5,
        'Bucharest': 6,
        'Tallinn': 7,
        'Valencia': 8,
        'Vienna': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [2, 3, 4, 9],  # Venice
        1: [2, 9],  # Reykjavik
        2: [0, 3, 4, 5, 6, 7, 8, 9],  # Munich
        3: [0, 2, 4, 6, 9],  # Santorini
        4: [0, 2, 3, 5, 6, 9],  # Manchester
        5: [2, 4, 8, 9],  # Porto
        6: [2, 3, 4, 7, 8, 9],  # Bucharest
        7: [2],  # Tallinn
        8: [2, 5, 6, 9],  # Valencia
        9: [0, 1, 2, 3, 4, 5, 6, 8]  # Vienna
    }
    
    # Required days in each city
    required_days = {
        0: 3,  # Venice
        1: 2,  # Reykjavik
        2: 3,  # Munich
        3: 3,  # Santorini
        4: 3,  # Manchester
        5: 3,  # Porto
        6: 5,  # Bucharest
        7: 4,  # Tallinn
        8: 2,  # Valencia
        9: 5   # Vienna
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..24)
    days = [Int(f'day_{i}') for i in range(24)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 10 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: annual show in Munich between days 4-6 (days 3-5 in 0-based)
    for i in range(3, 6):
        s.add(days[i] == 2)
    
    # Constraint: visit relatives in Santorini between days 8-10 (days 7-9 in 0-based)
    for i in range(7, 10):
        s.add(days[i] == 3)
    
    # Constraint: workshop in Valencia between days 14-15 (days 13-14 in 0-based)
    s.add(days[13] == 8)
    s.add(days[14] == 8)
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(23):
        current_city = days[i]
        next_city = days[i+1]
        s.add(Or(next_city == current_city, 
                 And(next_city != current_city, 
                     Or([next_city == dest for dest in direct_flights[current_city]])))
    
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
        for i in range(24):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()