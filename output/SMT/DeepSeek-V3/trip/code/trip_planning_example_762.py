from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Dublin': 0,
        'Madrid': 1,
        'Oslo': 2,
        'London': 3,
        'Vilnius': 4,
        'Berlin': 5
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 2, 3, 5],  # Dublin
        1: [0, 2, 3, 5],  # Madrid
        2: [0, 1, 3, 4, 5],  # Oslo
        3: [0, 1, 2, 5],  # London
        4: [2, 5],  # Vilnius
        5: [0, 1, 2, 3, 4]  # Berlin
    }
    
    # Required days in each city
    required_days = {
        0: 3,  # Dublin
        1: 2,  # Madrid
        2: 3,  # Oslo
        3: 2,  # London
        4: 3,  # Vilnius
        5: 5   # Berlin
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..13)
    days = [Int(f'day_{i}') for i in range(13)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 6 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: meet friends in Dublin between days 7-9 (days 6-8 in 0-based)
    s.add(Or([days[i] == 0 for i in range(6, 9)]))
    
    # Constraint: visit relatives in Madrid between days 2-3 (days 1-2 in 0-based)
    s.add(Or([days[i] == 1 for i in range(1, 3)]))
    
    # Constraint: wedding in Berlin between days 3-7 (days 2-6 in 0-based)
    s.add(Or([days[i] == 5 for i in range(2, 7)]))
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(12):
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
        for i in range(13):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()