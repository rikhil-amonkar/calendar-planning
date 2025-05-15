from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Manchester': 0,
        'Istanbul': 1,
        'Venice': 2,
        'Krakow': 3,
        'Lyon': 4
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 2, 3],  # Manchester
        1: [0, 2, 3, 4],  # Istanbul
        2: [0, 1, 4],  # Venice
        3: [0, 1],  # Krakow
        4: [1, 2]  # Lyon
    }
    
    # Required days in each city
    required_days = {
        0: 3,  # Manchester
        1: 7,  # Istanbul
        2: 7,  # Venice
        3: 6,  # Krakow
        4: 2   # Lyon
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..21)
    days = [Int(f'day_{i}') for i in range(21)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 5 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: wedding in Manchester between days 1-3 (days 0-2 in 0-based)
    for i in range(3):
        s.add(days[i] == 0)
    
    # Constraint: workshop in Venice between days 3-9 (days 2-8 in 0-based)
    for i in range(2, 9):
        s.add(days[i] == 2)
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(20):
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
        for i in range(21):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()