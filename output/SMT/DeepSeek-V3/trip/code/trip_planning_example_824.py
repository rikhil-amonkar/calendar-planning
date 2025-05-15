from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Berlin': 0,
        'Split': 1,
        'Bucharest': 2,
        'Riga': 3,
        'Lisbon': 4,
        'Tallinn': 5,
        'Lyon': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 3, 4, 5],  # Berlin
        1: [0, 6],  # Split
        2: [3, 4, 6],  # Bucharest
        3: [0, 2, 4, 5],  # Riga
        4: [0, 2, 3, 6],  # Lisbon
        5: [0, 3],  # Tallinn
        6: [1, 2, 4]  # Lyon
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Berlin
        1: 3,  # Split
        2: 3,  # Bucharest
        3: 5,  # Riga
        4: 3,  # Lisbon
        5: 4,  # Tallinn
        6: 5   # Lyon
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..22)
    days = [Int(f'day_{i}') for i in range(22)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 7 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: annual show in Berlin between days 1-5 (days 0-4 in 0-based)
    for i in range(5):
        s.add(days[i] == 0)
    
    # Constraint: wedding in Lyon between days 7-11 (days 6-10 in 0-based)
    for i in range(6, 11):
        s.add(days[i] == 6)
    
    # Constraint: visit relatives in Bucharest between days 13-15 (days 12-14 in 0-based)
    for i in range(12, 15):
        s.add(days[i] == 2)
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(21):
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
        for i in range(22):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()