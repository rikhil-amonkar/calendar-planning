from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Krakow': 0,
        'Frankfurt': 1,
        'Oslo': 2,
        'Dubrovnik': 3,
        'Naples': 4
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 2],  # Krakow
        1: [0, 2, 3, 4],  # Frankfurt
        2: [0, 1, 3, 4],  # Oslo
        3: [1, 2, 4],  # Dubrovnik
        4: [1, 2, 3]  # Naples
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Krakow
        1: 4,  # Frankfurt
        2: 3,  # Oslo
        3: 5,  # Dubrovnik
        4: 5   # Naples
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..18)
    days = [Int(f'day_{i}') for i in range(18)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 5 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: meet friends in Dubrovnik between days 5-9 (days 4-8 in 0-based)
    for i in range(4, 9):
        s.add(days[i] == 3)
    
    # Constraint: visit relatives in Oslo between days 16-18 (days 15-17 in 0-based)
    for i in range(15, 18):
        s.add(days[i] == 2)
    
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