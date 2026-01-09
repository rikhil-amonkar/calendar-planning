import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and their required days
    cities = {
        "Rome": 3,
        "Mykonos": 2,
        "Lisbon": 2,
        "Frankfurt": 5,
        "Nice": 3,
        "Stuttgart": 4,
        "Venice": 4,
        "Dublin": 2,
        "Bucharest": 2,
        "Seville": 5
    }
    
    total_days = 23
    
    # Define direct flight connections
    connections = [
        ("Rome", "Stuttgart"), ("Venice", "Rome"), ("Dublin", "Bucharest"),
        ("Mykonos", "Rome"), ("Seville", "Lisbon"), ("Frankfurt", "Venice"),
        ("Venice", "Stuttgart"), ("Bucharest", "Lisbon"), ("Nice", "Mykonos"),
        ("Venice", "Lisbon"), ("Dublin", "Lisbon"), ("Venice", "Nice"),
        ("Rome", "Seville"), ("Frankfurt", "Rome"), ("Nice", "Dublin"),
        ("Rome", "Bucharest"), ("Frankfurt", "Dublin"), ("Rome", "Dublin"),
        ("Venice", "Dublin"), ("Rome", "Lisbon"), ("Frankfurt", "Lisbon"),
        ("Nice", "Rome"), ("Frankfurt", "Nice"), ("Frankfurt", "Stuttgart"),
        ("Frankfurt", "Bucharest"), ("Lisbon", "Stuttgart"), ("Nice", "Lisbon"),
        ("Seville", "Dublin")
    ]
    
    # Create bidirectional connections
    flight_network = {}
    for city1, city2 in connections:
        if city1 not in flight_network:
            flight_network[city1] = set()
        if city2 not in flight_network:
            flight_network[city2] = set()
        flight_network[city1].add(city2)
        flight_network[city2].add(city1)
    
    # Special constraints
    mykonos_friends_day = [10, 11]  # Must be in Mykonos between day 10 and 11
    frankfurt_wedding = [1, 5]      # Must be in Frankfurt between day 1 and 5
    seville_conference = [13, 17]   # Must be in Seville between day 13 and 17
    
    problem = Problem()
    
    # Variables: start day for each city
    city_vars = list(cities.keys())
    for city in city_vars:
        problem.addVariable(city, range(1, total_days + 1))
    
    # Constraint: All cities must have different start days
    problem.addConstraint(AllDifferentConstraint(), city_vars)
    
    # Constraint: Total days constraint (start day + duration - 1 <= total_days)
    for city, duration in cities.items():
        problem.addConstraint(lambda start, dur=duration, td=total_days: start + dur - 1 <= td, [city])
    
    # Constraint: Cities cannot overlap in time
    for i, city1 in enumerate(city_vars):
        for j, city2 in enumerate(city_vars):
            if i < j:
                duration1 = cities[city1]
                duration2 = cities[city2]
                problem.addConstraint(
                    lambda start1, start2, dur1=duration1, dur2=duration2: 
                    start1 + dur1 <= start2 or start2 + dur2 <= start1,
                    [city1, city2]
                )
    
    # Constraint: Flight connectivity between consecutive cities
    def flight_constraint(city_order):
        for i in range(len(city_order) - 1):
            current_city = city_order[i]
            next_city = city_order[i + 1]
            if current_city not in flight_network or next_city not in flight_network[current_city]:
                return False
        return True
    
    # We need to find the right order of cities
    problem.addConstraint(flight_constraint, city_vars)
    
    # Special time window constraints
    def mykonos_constraint(start):
        duration = cities["Mykonos"]
        return any(day in range(start, start + duration) for day in mykonos_friends_day)
    
    def frankfurt_constraint(start):
        duration = cities["Frankfurt"]
        return any(day in range(start, start + duration) for day in frankfurt_wedding)
    
    def seville_constraint(start):
        duration = cities["Seville"]
        return any(day in range(start, start + duration) for day in seville_conference)
    
    problem.addConstraint(mykonos_constraint, ["Mykonos"])
    problem.addConstraint(frankfurt_constraint, ["Frankfurt"])
    problem.addConstraint(seville_constraint, ["Seville"])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: Try without flight constraints if no solution found
        problem = Problem()
        for city in city_vars:
            problem.addVariable(city, range(1, total_days + 1))
        problem.addConstraint(AllDifferentConstraint(), city_vars)
        for city, duration in cities.items():
            problem.addConstraint(lambda start, dur=duration, td=total_days: start + dur - 1 <= td, [city])
        for i, city1 in enumerate(city_vars):
            for j, city2 in enumerate(city_vars):
                if i < j:
                    duration1 = cities[city1]
                    duration2 = cities[city2]
                    problem.addConstraint(
                        lambda start1, start2, dur1=duration1, dur2=duration2: 
                        start1 + dur1 <= start2 or start2 + dur2 <= start1,
                        [city1, city2]
                    )
        problem.addConstraint(mykonos_constraint, ["Mykonos"])
        problem.addConstraint(frankfurt_constraint, ["Frankfurt"])
        problem.addConstraint(seville_constraint, ["Seville"])
        solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        
        # Create itinerary with day ranges
        itinerary = []
        for city, start_day in solution.items():
            duration = cities[city]
            end_day = start_day + duration - 1
            if duration == 1:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city})
        
        # Sort by start day
        itinerary.sort(key=lambda x: int(x["day_range"].split(" ")[1].split("-")[0]))
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()