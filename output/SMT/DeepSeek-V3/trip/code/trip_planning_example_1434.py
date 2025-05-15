from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Rome': 0,
        'Mykonos': 1,
        'Lisbon': 2,
        'Frankfurt': 3,
        'Nice': 4,
        'Stuttgart': 5,
        'Venice': 6,
        'Dublin': 7,
        'Bucharest': 8,
        'Seville': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 3, 4, 5, 6, 7, 8, 9],  # Rome
        1: [0, 4],  # Mykonos
        2: [3, 5, 6, 7, 8, 9],  # Lisbon
        3: [0, 4, 5, 6, 7, 8, 9],  # Frankfurt
        4: [0, 1, 3, 6, 7, 9],  # Nice
        5: [0, 3, 6, 9],  # Stuttgart
        6: [0, 2, 3, 4, 5, 7, 9],  # Venice
        7: [2, 3, 4, 6, 8, 9],  # Dublin
        8: [0, 2, 3, 7],  # Bucharest
        9: [0, 2, 3, 4, 5, 6, 7]  # Seville
    }
    
    # Required days in each city
    required_days = {
        0: 3,  # Rome
        1: 2,  # Mykonos
        2: 2,  # Lisbon
        3: 5,  # Frankfurt
        4: 3,  # Nice
        5: 4,  # Stuttgart
        6: 4,  # Venice
        7: 2,  # Dublin
        8: 2,  # Bucharest
        9: 5   # Seville
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..23)
    days = [Int(f'day_{i}') for i in range(23)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 10 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: wedding in Frankfurt between days 1-5 (days 0-4 in 0-based)
    for i in range(5):
        s.add(days[i] == 3)
    
    # Constraint: meet friends in Mykonos between days 10-11 (days 9-10 in 0-based)
    s.add(Or(days[9] == 1, days[10] == 1))
    
    # Constraint: conference in Seville between days 13-17 (days 12-16 in 0-based)
    for i in range(12, 17):
        s.add(days[i] == 9)
    
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