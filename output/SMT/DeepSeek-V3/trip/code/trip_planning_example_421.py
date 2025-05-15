from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Nice': 0,
        'Krakow': 1,
        'Dublin': 2,
        'Lyon': 3,
        'Frankfurt': 4
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [2, 3, 4],  # Nice
        1: [2, 4],  # Krakow
        2: [0, 1, 3, 4],  # Dublin
        3: [0, 2, 4],  # Lyon
        4: [0, 1, 2, 3]  # Frankfurt
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Nice
        1: 6,  # Krakow
        2: 7,  # Dublin
        3: 4,  # Lyon
        4: 2   # Frankfurt
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..20)
    days = [Int(f'day_{i}') for i in range(20)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 5 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: relatives in Nice between days 1-5 (days 0-4 in 0-based)
    for i in range(5):
        s.add(days[i] == 0)
    
    # Constraint: meet friends in Frankfurt between days 19-20 (days 18-19 in 0-based)
    s.add(days[18] == 4)
    s.add(days[19] == 4)
    
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