from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Copenhagen': 0,
        'Geneva': 1,
        'Mykonos': 2,
        'Naples': 3,
        'Prague': 4,
        'Dubrovnik': 5,
        'Athens': 6,
        'Santorini': 7,
        'Brussels': 8,
        'Munich': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 3, 4, 5, 6, 7, 8, 9],  # Copenhagen
        1: [0, 2, 3, 4, 5, 6, 7, 8, 9],  # Geneva
        2: [1, 3, 6, 9],  # Mykonos
        3: [0, 1, 2, 5, 6, 7, 8, 9],  # Naples
        4: [0, 1, 6, 8, 9],  # Prague
        5: [0, 1, 3, 6, 9],  # Dubrovnik
        6: [0, 1, 2, 3, 4, 5, 7, 8, 9],  # Athens
        7: [0, 1, 3, 6],  # Santorini
        8: [0, 1, 3, 4, 6, 9],  # Brussels
        9: [0, 1, 2, 3, 4, 5, 6, 8]  # Munich
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Copenhagen
        1: 3,  # Geneva
        2: 2,  # Mykonos
        3: 4,  # Naples
        4: 2,  # Prague
        5: 3,  # Dubrovnik
        6: 4,  # Athens
        7: 5,  # Santorini
        8: 4,  # Brussels
        9: 5   # Munich
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..28)
    days = [Int(f'day_{i}') for i in range(28)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 10 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: meet friend in Copenhagen between days 11-15 (days 10-14 in 0-based)
    for i in range(10, 15):
        s.add(days[i] == 0)
    
    # Constraint: conference in Mykonos between days 27-28 (days 26-27 in 0-based)
    s.add(days[26] == 2)
    s.add(days[27] == 2)
    
    # Constraint: visit relatives in Naples between days 5-8 (days 4-7 in 0-based)
    for i in range(4, 8):
        s.add(days[i] == 3)
    
    # Constraint: workshop in Athens between days 8-11 (days 7-10 in 0-based)
    for i in range(7, 11):
        s.add(days[i] == 6)
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(27):
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
        for i in range(28):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()