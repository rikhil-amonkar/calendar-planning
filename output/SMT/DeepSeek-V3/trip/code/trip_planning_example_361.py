from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Paris': 0,
        'Madrid': 1,
        'Bucharest': 2,
        'Seville': 3
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 2, 3],  # Paris
        1: [0, 2, 3],  # Madrid
        2: [0, 1],  # Bucharest
        3: [0, 1]  # Seville
    }
    
    # Required days in each city
    required_days = {
        0: 6,  # Paris
        1: 7,  # Madrid
        2: 2,  # Bucharest
        3: 3   # Seville
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..15)
    days = [Int(f'day_{i}') for i in range(15)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 4 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: annual show in Madrid between days 1-7 (days 0-6 in 0-based)
    for i in range(7):
        s.add(days[i] == 1)
    
    # Constraint: visit relatives in Bucharest between days 14-15 (days 13-14 in 0-based)
    s.add(days[13] == 2)
    s.add(days[14] == 2)
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(14):
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
        for i in range(15):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()