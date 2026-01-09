import constraint
import json

def main():
    problem = constraint.Problem()
    
    # Cities and their required days
    cities = {
        'Naples': 3,
        'Valencia': 5,
        'Stuttgart': 2,
        'Split': 5,
        'Venice': 5,
        'Amsterdam': 4,
        'Nice': 2,
        'Barcelona': 2,
        'Porto': 4
    }
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Venice', 'Nice'), ('Naples', 'Amsterdam'), ('Barcelona', 'Nice'),
        ('Amsterdam', 'Nice'), ('Stuttgart', 'Valencia'), ('Stuttgart', 'Porto'),
        ('Split', 'Stuttgart'), ('Split', 'Naples'), ('Valencia', 'Amsterdam'),
        ('Barcelona', 'Porto'), ('Valencia', 'Naples'), ('Venice', 'Amsterdam'),
        ('Barcelona', 'Naples'), ('Barcelona', 'Valencia'), ('Split', 'Amsterdam'),
        ('Barcelona', 'Venice'), ('Stuttgart', 'Amsterdam'), ('Naples', 'Nice'),
        ('Venice', 'Stuttgart'), ('Split', 'Barcelona'), ('Porto', 'Nice'),
        ('Barcelona', 'Stuttgart'), ('Venice', 'Naples'), ('Porto', 'Amsterdam'),
        ('Porto', 'Valencia'), ('Stuttgart', 'Naples'), ('Barcelona', 'Amsterdam')
    ]
    
    # Create bidirectional flights set
    flights_set = set()
    for city1, city2 in direct_flights:
        flights_set.add((city1, city2))
        flights_set.add((city2, city1))
    
    # Total days
    total_days = 24
    
    # Special constraints
    naples_friend_range = (18, 20)  # Must be in Naples between day 18-20
    venice_conference_range = (6, 10)  # Must be in Venice between day 6-10
    barcelona_workshop_range = (5, 6)  # Must be in Barcelona between day 5-6
    nice_friends_range = (23, 24)  # Must be in Nice between day 23-24
    
    # Variables: start day for each city stay
    for city in cities:
        problem.addVariable(f"{city}_start", range(1, total_days + 1))
    
    # Constraint: all stays must be within the 24-day period and respect durations
    for city, duration in cities.items():
        problem.addConstraint(
            lambda start, dur=duration: start >= 1 and start + dur - 1 <= total_days,
            [f"{city}_start"]
        )
    
    # Constraint: no overlapping stays
    city_list = list(cities.keys())
    for i in range(len(city_list)):
        for j in range(i + 1, len(city_list)):
            city1, city2 = city_list[i], city_list[j]
            dur1, dur2 = cities[city1], cities[city2]
            problem.addConstraint(
                lambda s1, s2, d1=dur1, d2=dur2: 
                    s1 + d1 <= s2 or s2 + d2 <= s1,
                [f"{city1}_start", f"{city2}_start"]
            )
    
    # Special date constraints
    # Naples: must include at least one day between 18-20
    problem.addConstraint(
        lambda start: any(day >= naples_friend_range[0] and day <= naples_friend_range[1] 
                         for day in range(start, start + cities['Naples'])),
        ["Naples_start"]
    )
    
    # Venice: must include all days between 6-10
    problem.addConstraint(
        lambda start: start <= venice_conference_range[0] and 
                     start + cities['Venice'] - 1 >= venice_conference_range[1],
        ["Venice_start"]
    )
    
    # Barcelona: must include both days 5 and 6
    problem.addConstraint(
        lambda start: start <= barcelona_workshop_range[0] and 
                     start + cities['Barcelona'] - 1 >= barcelona_workshop_range[1],
        ["Barcelona_start"]
    )
    
    # Nice: must include at least one day between 23-24
    problem.addConstraint(
        lambda start: any(day >= nice_friends_range[0] and day <= nice_friends_range[1] 
                         for day in range(start, start + cities['Nice'])),
        ["Nice_start"]
    )
    
    # Flight connectivity constraint - simplified approach
    # Instead of enforcing a strict order, we'll check that consecutive stays in time
    # have direct flight connections
    
    def check_flight_connectivity(*starts):
        # Create list of (start_day, city, duration)
        stays = []
        for i, city in enumerate(city_list):
            stays.append((starts[i], city, cities[city]))
        
        # Sort by start day to get chronological order
        stays.sort()
        
        # Check flight connectivity between consecutive stays
        for i in range(len(stays) - 1):
            current_city = stays[i][1]
            next_city = stays[i + 1][1]
            
            # Check if there's a direct flight between these cities
            if (current_city, next_city) not in flights_set:
                return False
        
        return True
    
    # Apply the flight connectivity constraint
    problem.addConstraint(
        check_flight_connectivity,
        [f"{city}_start" for city in city_list]
    )
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first solution
    solution = solutions[0]
    
    # Create itinerary with day ranges
    itinerary = []
    city_stays = []
    
    for city in cities:
        start = solution[f"{city}_start"]
        end = start + cities[city] - 1
        city_stays.append((start, end, city))
    
    # Sort by start day
    city_stays.sort()
    
    # Create the itinerary
    for start, end, city in city_stays:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()