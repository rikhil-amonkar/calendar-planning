from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Vienna': 0,
        'Barcelona': 1,
        'Edinburgh': 2,
        'Krakow': 3,
        'Riga': 4,
        'Hamburg': 5,
        'Paris': 6,
        'Stockholm': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 3, 4, 5, 6, 7],  # Vienna
        1: [0, 2, 3, 4, 5, 6, 7],  # Barcelona
        2: [1, 3, 4, 5, 6, 7],  # Edinburgh
        3: [0, 1, 2, 4, 6, 7],  # Krakow
        4: [0, 1, 2, 3, 5, 6, 7],  # Riga
        5: [0, 1, 2, 4, 6, 7],  # Hamburg
        6: [0, 1, 2, 3, 4, 5, 7],  # Paris
        7: [0, 1, 2, 3, 4, 5, 6]  # Stockholm
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Vienna
        1: 2,  # Barcelona
        2: 4,  # Edinburgh
        3: 3,  # Krakow
        4: 4,  # Riga
        5: 2,  # Hamburg
        6: 2,  # Paris
        7: 2   # Stockholm
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..16)
    days = [Int(f'day_{i}') for i in range(16)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 8 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: wedding in Paris between days 1-2 (days 0-1 in 0-based)
    s.add(days[0] == 6)
    s.add(days[1] == 6)
    
    # Constraint: conference in Hamburg between days 10-11 (days 9-10 in 0-based)
    s.add(days[9] == 5)
    s.add(days[10] == 5)
    
    # Constraint: meet friend in Edinburgh between days 12-15 (days 11-14 in 0-based)
    for i in range(11, 15):
        s.add(days[i] == 2)
    
    # Constraint: visit relatives in Stockholm between days 15-16 (days 14-15 in 0-based)
    s.add(days[14] == 7)
    s.add(days[15] == 7)
    
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