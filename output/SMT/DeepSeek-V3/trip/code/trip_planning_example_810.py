from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Berlin': 0,
        'Nice': 1,
        'Athens': 2,
        'Stockholm': 3,
        'Barcelona': 4,
        'Vilnius': 5,
        'Lyon': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 2, 3, 4, 5],  # Berlin
        1: [0, 2, 3, 4, 6],  # Nice
        2: [0, 1, 3, 4, 5],  # Athens
        3: [0, 1, 2, 4],  # Stockholm
        4: [0, 1, 2, 3, 6],  # Barcelona
        5: [0, 2],  # Vilnius
        6: [1, 4]  # Lyon
    }
    
    # Required days in each city
    required_days = {
        0: 3,  # Berlin
        1: 5,  # Nice
        2: 5,  # Athens
        3: 5,  # Stockholm
        4: 2,  # Barcelona
        5: 4,  # Vilnius
        6: 2   # Lyon
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..20)
    days = [Int(f'day_{i}') for i in range(20)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 7 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: conference in Berlin between days 1-3 (days 0-2 in 0-based)
    for i in range(3):
        s.add(days[i] == 0)
    
    # Constraint: workshop in Barcelona between days 3-4 (days 2-3 in 0-based)
    s.add(days[2] == 4)
    s.add(days[3] == 4)
    
    # Constraint: wedding in Lyon between days 4-5 (days 3-4 in 0-based)
    s.add(days[3] == 6)
    s.add(days[4] == 6)
    
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