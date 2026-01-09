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
    
    # Direct flights
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
    
    # Create bidirectional flights
    flights_set = set()
    for city1, city2 in direct_flights:
        flights_set.add((city1, city2))
        flights_set.add((city2, city1))
    direct_flights = list(flights_set)
    
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
        problem.addVariable(f"{city}_end", range(1, total_days + 1))
    
    # Constraint: end day = start day + duration - 1
    for city, duration in cities.items():
        problem.addConstraint(
            lambda start, end, dur=duration: end == start + dur - 1,
            [f"{city}_start", f"{city}_end"]
        )
    
    # Constraint: all stays must be within the 24-day period
    for city in cities:
        problem.addConstraint(
            lambda start, end: start >= 1 and end <= total_days,
            [f"{city}_start", f"{city}_end"]
        )
    
    # Constraint: no overlapping stays (cities are visited sequentially)
    city_list = list(cities.keys())
    for i in range(len(city_list)):
        for j in range(i + 1, len(city_list)):
            city1, city2 = city_list[i], city_list[j]
            problem.addConstraint(
                lambda s1, e1, s2, e2: e1 < s2 or e2 < s1,
                [f"{city1}_start", f"{city1}_end", f"{city2}_start", f"{city2}_end"]
            )
    
    # Special date constraints
    # Naples: must include at least one day between 18-20
    problem.addConstraint(
        lambda start, end: any(day >= naples_friend_range[0] and day <= naples_friend_range[1] 
                              for day in range(start, end + 1)),
        ["Naples_start", "Naples_end"]
    )
    
    # Venice: must include all days between 6-10
    problem.addConstraint(
        lambda start, end: start <= venice_conference_range[0] and end >= venice_conference_range[1],
        ["Venice_start", "Venice_end"]
    )
    
    # Barcelona: must include both days 5 and 6
    problem.addConstraint(
        lambda start, end: start <= barcelona_workshop_range[0] and end >= barcelona_workshop_range[1],
        ["Barcelona_start", "Barcelona_end"]
    )
    
    # Nice: must include at least one day between 23-24
    problem.addConstraint(
        lambda start, end: any(day >= nice_friends_range[0] and day <= nice_friends_range[1] 
                              for day in range(start, end + 1)),
        ["Nice_start", "Nice_end"]
    )
    
    # Constraint: consecutive cities must have direct flights
    def has_flight(city1_end, city2_start, city1_name, city2_name):
        if city2_start == city1_end + 1:  # Consecutive cities
            return (city1_name, city2_name) in direct_flights
        return True
    
    for i in range(len(city_list)):
        for j in range(len(city_list)):
            if i != j:
                city1, city2 = city_list[i], city_list[j]
                problem.addConstraint(
                    lambda e1, s2, c1=city1, c2=city2: has_flight(e1, s2, c1, c2),
                    [f"{city1}_end", f"{city2}_start"]
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
        end = solution[f"{city}_end"]
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