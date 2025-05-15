from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Oslo': 0,
        'Stuttgart': 1,
        'Venice': 2,
        'Split': 3,
        'Barcelona': 4,
        'Brussels': 5,
        'Copenhagen': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [3, 4, 5, 6],  # Oslo
        1: [2, 4, 6],  # Stuttgart
        2: [1, 4, 5, 6],  # Venice
        3: [0, 4, 6],  # Split
        4: [0, 1, 2, 3, 5, 6],  # Barcelona
        5: [0, 2, 4, 6],  # Brussels
        6: [0, 1, 2, 3, 4, 5]  # Copenhagen
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Oslo
        1: 3,  # Stuttgart
        2: 4,  # Venice
        3: 4,  # Split
        4: 3,  # Barcelona
        5: 3,  # Brussels
        6: 3   # Copenhagen
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..16)
    days = [Int(f'day_{i}') for i in range(16)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 7 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: annual show in Barcelona between days 1-3 (days 0-2 in 0-based)
    for i in range(3):
        s.add(days[i] == 4)
    
    # Constraint: meet friends in Oslo between days 3-4 (days 2-3 in 0-based)
    s.add(days[2] == 0)
    s.add(days[3] == 0)
    
    # Constraint: meet friend in Brussels between days 9-11 (days 8-10 in 0-based)
    for i in range(8, 11):
        s.add(days[i] == 5)
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(15):
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
        for i in range(16):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()