from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Seville': 0,
        'Paris': 1,
        'Krakow': 2
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1],  # Seville
        1: [0, 2],  # Paris
        2: [1]  # Krakow
    }
    
    # Required days in each city
    required_days = {
        0: 6,  # Seville
        1: 2,  # Paris
        2: 5   # Krakow
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..11)
    days = [Int(f'day_{i}') for i in range(11)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 3 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: workshop in Krakow between days 1-5 (days 0-4 in 0-based)
    for i in range(5):
        s.add(days[i] == 2)
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(10):
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
        for i in range(11):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()