from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Prague': 0,
        'Brussels': 1,
        'Riga': 2,
        'Munich': 3,
        'Seville': 4,
        'Stockholm': 5,
        'Istanbul': 6,
        'Amsterdam': 7,
        'Vienna': 8,
        'Split': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 2, 3, 5, 6, 7, 8, 9],  # Prague
        1: [0, 2, 3, 4, 5, 6, 7, 8],  # Brussels
        2: [0, 1, 3, 5, 6, 7, 8],  # Riga
        3: [0, 1, 2, 4, 5, 6, 7, 9],  # Munich
        4: [1, 3, 5, 7, 8, 9],  # Seville
        5: [0, 1, 2, 3, 4, 6, 7, 8, 9],  # Stockholm
        6: [0, 1, 2, 3, 5, 7, 8],  # Istanbul
        7: [0, 1, 2, 3, 4, 5, 6, 8, 9],  # Amsterdam
        8: [0, 1, 2, 3, 4, 5, 6, 7, 9],  # Vienna
        9: [0, 3, 5, 7, 8]  # Split
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Prague
        1: 2,  # Brussels
        2: 2,  # Riga
        3: 2,  # Munich
        4: 3,  # Seville
        5: 2,  # Stockholm
        6: 2,  # Istanbul
        7: 3,  # Amsterdam
        8: 5,  # Vienna
        9: 3   # Split
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..20)
    days = [Int(f'day_{i}') for i in range(20)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 10 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: meet friend in Vienna between days 1-5 (days 0-4 in 0-based)
    for i in range(5):
        s.add(days[i] == 8)
    
    # Constraint: annual show in Prague between days 5-9 (days 4-8 in 0-based)
    for i in range(4, 9):
        s.add(days[i] == 0)
    
    # Constraint: visit relatives in Split between days 11-13 (days 10-12 in 0-based)
    for i in range(10, 13):
        s.add(days[i] == 9)
    
    # Constraint: meet friends in Riga between days 15-16 (days 14-15 in 0-based)
    s.add(Or(days[14] == 2, days[15] == 2))
    
    # Constraint: conference in Stockholm between days 16-17 (days 15-16 in 0-based)
    s.add(days[15] == 5)
    s.add(days[16] == 5)
    
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