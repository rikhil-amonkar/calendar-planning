from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Reykjavik': 0,
        'Stockholm': 1,
        'Oslo': 2,
        'Stuttgart': 3,
        'Tallinn': 4,
        'Split': 5,
        'Geneva': 6,
        'Porto': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 2, 3, 4],  # Reykjavik
        1: [0, 2, 3, 5, 6],  # Stockholm
        2: [0, 1, 5, 6, 7, 4],  # Oslo
        3: [0, 1, 5, 7],  # Stuttgart
        4: [0, 2],  # Tallinn
        5: [1, 2, 3, 6],  # Split
        6: [1, 2, 5, 7],  # Geneva
        7: [2, 3, 6]  # Porto
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Reykjavik
        1: 3,  # Stockholm
        2: 5,  # Oslo
        3: 5,  # Stuttgart
        4: 5,  # Tallinn
        5: 3,  # Split
        6: 2,  # Geneva
        7: 3   # Porto
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..21)
    days = [Int(f'day_{i}') for i in range(21)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 8 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: days 1 and 2 must be Reykjavik (0)
    s.add(days[0] == 0)
    s.add(days[1] == 0)
    
    # Constraint: days 19-21 must be Porto (7)
    s.add(Or(days[18] == 7, days[19] == 7, days[20] == 7))
    # Ensure all three days are Porto if the workshop spans all three days
    # Alternatively, the problem says "between day 19 and day 21", which could mean at least one day in Porto during 19-21
    # Assuming the workshop is attended on all three days (since the total days in Porto is 3)
    s.add(days[18] == 7)
    s.add(days[19] == 7)
    s.add(days[20] == 7)
    
    # Constraint: meet friend in Stockholm between day 2 and day 4 (i.e., days 3, 4, or 5 in 1-based)
    s.add(Or(days[2] == 1, days[3] == 1, days[4] == 1))
    
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