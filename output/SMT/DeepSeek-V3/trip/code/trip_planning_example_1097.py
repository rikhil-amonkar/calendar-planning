from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Reykjavik': 0,
        'Riga': 1,
        'Oslo': 2,
        'Lyon': 3,
        'Dubrovnik': 4,
        'Madrid': 5,
        'Warsaw': 6,
        'London': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [5, 6, 7],  # Reykjavik
        1: [2, 6],  # Riga
        2: [1, 4, 5, 6, 7, 3, 0],  # Oslo
        3: [5, 7],  # Lyon
        4: [2, 5],  # Dubrovnik
        5: [0, 2, 3, 6, 7],  # Madrid
        6: [0, 1, 2, 5, 7],  # Warsaw
        7: [0, 2, 3, 5, 6]  # London
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Reykjavik
        1: 2,  # Riga
        2: 3,  # Oslo
        3: 5,  # Lyon
        4: 2,  # Dubrovnik
        5: 2,  # Madrid
        6: 4,  # Warsaw
        7: 3   # London
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..18)
    days = [Int(f'day_{i}') for i in range(18)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 8 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: meet friend in Riga between days 4-5 (days 3-4 in 0-based)
    s.add(Or(days[3] == 1, days[4] == 1))
    
    # Constraint: wedding in Dubrovnik between days 7-8 (days 6-7 in 0-based)
    s.add(Or(days[6] == 4, days[7] == 4))
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(17):
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
        for i in range(18):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()