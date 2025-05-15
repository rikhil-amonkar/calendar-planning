from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Santorini': 0,
        'Krakow': 1,
        'Paris': 2,
        'Vilnius': 3,
        'Munich': 4,
        'Geneva': 5,
        'Amsterdam': 6,
        'Budapest': 7,
        'Split': 8
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [5, 6],  # Santorini
        1: [2, 3, 4, 6, 8],  # Krakow
        2: [1, 3, 5, 6, 7, 8],  # Paris
        3: [1, 2, 4, 6, 8],  # Vilnius
        4: [1, 3, 5, 6, 7, 8],  # Munich
        5: [0, 2, 4, 6, 7, 8],  # Geneva
        6: [0, 1, 2, 3, 4, 5, 7, 8],  # Amsterdam
        7: [2, 4, 5, 6],  # Budapest
        8: [1, 2, 3, 4, 5, 6]  # Split
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Santorini
        1: 5,  # Krakow
        2: 5,  # Paris
        3: 3,  # Vilnius
        4: 5,  # Munich
        5: 2,  # Geneva
        6: 4,  # Amsterdam
        7: 5,  # Budapest
        8: 4   # Split
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..30)
    days = [Int(f'day_{i}') for i in range(30)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 9 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: meet friends in Santorini between days 25-29 (days 24-28 in 0-based)
    for i in range(24, 29):
        s.add(days[i] == 0)
    
    # Constraint: wedding in Krakow between days 18-22 (days 17-21 in 0-based)
    for i in range(17, 22):
        s.add(days[i] == 1)
    
    # Constraint: meet friend in Paris between days 11-15 (days 10-14 in 0-based)
    for i in range(10, 15):
        s.add(days[i] == 2)
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(29):
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
        for i in range(30):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()