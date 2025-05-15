from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Oslo': 0,
        'Reykjavik': 1,
        'Stockholm': 2,
        'Munich': 3,
        'Frankfurt': 4,
        'Barcelona': 5,
        'Bucharest': 6,
        'Split': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 3, 4, 5, 6, 7],  # Oslo
        1: [0, 3, 4, 5, 2],  # Reykjavik
        2: [1, 3, 4, 5, 7],  # Stockholm
        3: [0, 1, 4, 5, 6, 7],  # Munich
        4: [0, 1, 2, 3, 5, 6, 7],  # Frankfurt
        5: [0, 1, 2, 3, 4, 6, 7],  # Barcelona
        6: [0, 3, 4, 5],  # Bucharest
        7: [0, 2, 3, 4, 5]  # Split
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Oslo
        1: 5,  # Reykjavik
        2: 4,  # Stockholm
        3: 4,  # Munich
        4: 4,  # Frankfurt
        5: 3,  # Barcelona
        6: 2,  # Bucharest
        7: 3   # Split
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..20)
    days = [Int(f'day_{i}') for i in range(20)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 8 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: annual show in Oslo between days 16-17 (days 15-16 in 0-based)
    s.add(days[15] == 0)
    s.add(days[16] == 0)
    
    # Constraint: meet friend in Reykjavik between days 9-13 (days 8-12 in 0-based)
    s.add(Or([days[i] == 1 for i in range(8, 13)]))
    
    # Constraint: visit relatives in Munich between days 13-16 (days 12-15 in 0-based)
    s.add(Or([days[i] == 3 for i in range(12, 16)]))
    
    # Constraint: workshop in Frankfurt between days 17-20 (days 16-19 in 0-based)
    for i in range(16, 20):
        s.add(days[i] == 4)
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(19):
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
        for i in range(20):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()