import json
from constraint import Problem

def solve_itinerary():
    # Define the problem
    problem = Problem()
    
    # Cities and their required stay durations
    cities = {
        'Porto': 3,
        'Stuttgart': 7,
        'Seville': 2,
        'Madrid': 4
    }
    
    total_days = 13
    
    # Define arrival day for each city (0 means not visited)
    for city in cities:
        problem.addVariable(f'arrive_{city}', range(1, total_days + 1))
    
    # Constraints
    # 1. Stuttgart conference on day 7 and day 13
    # This means we must be in Stuttgart on both these days
    problem.addConstraint(lambda a: a <= 7 and a + 6 >= 13, ['arrive_Stuttgart'])
    
    # 2. Visit relatives in Madrid between day 1 and day 4
    # This means the Madrid visit must start and end within days 1-4
    problem.addConstraint(lambda a: a == 1, ['arrive_Madrid'])  # Must start on day 1 to fit 4 days
    
    # 3. No overlapping stays
    def no_overlap(*arrivals):
        # Check if any two cities overlap
        city_arrivals = list(zip(cities.keys(), arrivals))
        
        for i, (city1, arrive1) in enumerate(city_arrivals):
            depart1 = arrive1 + cities[city1] - 1
            for j, (city2, arrive2) in enumerate(city_arrivals):
                if i < j:  # Avoid duplicate checks
                    depart2 = arrive2 + cities[city2] - 1
                    # Check if the two stays overlap
                    if not (depart1 < arrive2 or depart2 < arrive1):
                        return False
        
        # Check if all days are covered exactly once
        days_covered = set()
        for city, arrive in city_arrivals:
            depart = arrive + cities[city] - 1
            for day in range(arrive, depart + 1):
                if day in days_covered:
                    return False
                days_covered.add(day)
        
        return len(days_covered) == total_days and min(days_covered) == 1 and max(days_covered) == total_days
    
    arrival_vars = [f'arrive_{city}' for city in cities]
    problem.addConstraint(no_overlap, arrival_vars)
    
    # 4. Direct flight constraints
    direct_flights = {
        'Porto': ['Stuttgart', 'Seville', 'Madrid'],
        'Stuttgart': ['Porto'],
        'Seville': ['Porto', 'Madrid'],
        'Madrid': ['Porto', 'Seville']
    }
    
    def valid_transitions(*arrivals):
        city_arrivals = list(zip(cities.keys(), arrivals))
        # Sort by arrival day
        city_arrivals.sort(key=lambda x: x[1])
        
        # Check transitions between consecutive cities
        for i in range(len(city_arrivals) - 1):
            city1, arrive1 = city_arrivals[i]
            city2, arrive2 = city_arrivals[i + 1]
            depart1 = arrive1 + cities[city1] - 1
            
            # Cities must be consecutive (no gaps)
            if depart1 + 1 != arrive2:
                return False
            
            # Check if direct flight exists
            if city2 not in direct_flights.get(city1, []):
                return False
        
        return True
    
    problem.addConstraint(valid_transitions, arrival_vars)
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first solution
    solution = solutions[0]
    
    # Build itinerary
    itinerary = []
    city_stays = []
    
    for city in cities:
        arrive = solution[f'arrive_{city}']
        depart = arrive + cities[city] - 1
        city_stays.append({
            'city': city,
            'arrive': arrive,
            'depart': depart
        })
    
    # Sort by arrival day
    city_stays.sort(key=lambda x: x['arrive'])
    
    # Create day ranges
    for stay in city_stays:
        if stay['arrive'] == stay['depart']:
            day_range = f"Day {stay['arrive']}"
        else:
            day_range = f"Day {stay['arrive']}-{stay['depart']}"
        
        itinerary.append({
            'day_range': day_range,
            'place': stay['city']
        })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))