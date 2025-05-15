from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Lyon': 0,
        'Paris': 1,
        'Riga': 2,
        'Berlin': 3,
        'Stockholm': 4,
        'Zurich': 5,
        'Nice': 6,
        'Seville': 7,
        'Milan': 8,
        'Naples': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 6],  # Lyon
        1: [0, 2, 4, 5, 6, 7, 8, 9],  # Paris
        2: [1, 3, 4, 5, 6, 8],  # Riga
        3: [1, 2, 4, 5, 6, 8, 9],  # Berlin
        4: [1, 2, 3, 5, 6, 8],  # Stockholm
        5: [1, 2, 3, 4, 6, 8, 9],  # Zurich
        6: [0, 1, 2, 3, 4, 5, 8, 9],  # Nice
        7: [1, 8],  # Seville
        8: [1, 2, 3, 4, 5, 6, 7, 9],  # Milan
        9: [1, 3, 5, 6, 8]  # Naples
    }
    
    # Required days in each city
    required_days = {
        0: 3,  # Lyon
        1: 5,  # Paris
        2: 2,  # Riga
        3: 2,  # Berlin
        4: 3,  # Stockholm
        5: 5,  # Zurich
        6: 2,  # Nice
        7: 3,  # Seville
        8: 3,  # Milan
        9: 4   # Naples
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..23)
    days = [Int(f'day_{i}') for i in range(23)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 10 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: wedding in Berlin between days 1-2 (days 0-1 in 0-based)
    s.add(days[0] == 3)
    s.add(days[1] == 3)
    
    # Constraint: annual show in Stockholm between days 20-22 (days 19-21 in 0-based)
    for i in range(19, 22):
        s.add(days[i] == 4)
    
    # Constraint: workshop in Nice between days 12-13 (days 11-12 in 0-based)
    s.add(days[11] == 6)
    s.add(days[12] == 6)
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(22):
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
        for i in range(23):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()