import json
from constraint import Problem

def solve_itinerary():
    # Define the problem
    problem = Problem()
    
    # Cities
    cities = ['Porto', 'Stuttgart', 'Seville', 'Madrid']
    
    # Total days
    total_days = 13
    
    # Define variables for arrival day in each city
    # We'll use -1 to indicate the city is not visited
    for city in cities:
        problem.addVariable(f'arrive_{city}', range(-1, total_days + 1))
        problem.addVariable(f'depart_{city}', range(-1, total_days + 1))
        problem.addVariable(f'days_{city}', range(0, total_days + 1))
    
    # Fixed constraints from the problem statement
    # Stay in Seville for 2 days
    problem.addConstraint(lambda days: days == 2, ['days_Seville'])
    
    # Stay in Stuttgart for 7 days
    problem.addConstraint(lambda days: days == 7, ['days_Stuttgart'])
    
    # Conference in Stuttgart on day 7 and day 13
    problem.addConstraint(lambda arrive, depart: arrive <= 7 and depart >= 13, 
                         ['arrive_Stuttgart', 'depart_Stuttgart'])
    
    # Visit Porto for 3 days
    problem.addConstraint(lambda days: days == 3, ['days_Porto'])
    
    # Visit Madrid for 4 days
    problem.addConstraint(lambda days: days == 4, ['days_Madrid'])
    
    # Visit relatives in Madrid between day 1 and day 4
    problem.addConstraint(lambda arrive, depart: arrive >= 1 and depart <= 4, 
                         ['arrive_Madrid', 'depart_Madrid'])
    
    # All cities must be visited (arrival day >= 0)
    for city in cities:
        problem.addConstraint(lambda arrive: arrive >= 0, [f'arrive_{city}'])
    
    # Departure day must be >= arrival day
    for city in cities:
        problem.addConstraint(lambda arrive, depart, days: 
                             depart == arrive + days - 1 if arrive >= 0 else True,
                             [f'arrive_{city}', f'depart_{city}', f'days_{city}'])
    
    # Direct flight constraints
    direct_flights = {
        'Porto': ['Stuttgart', 'Seville', 'Madrid'],
        'Stuttgart': ['Porto'],
        'Seville': ['Porto', 'Madrid'],
        'Madrid': ['Porto', 'Seville']
    }
    
    # Ensure travel only between cities with direct flights
    def valid_transition(arrive_city1, depart_city1, arrive_city2, depart_city2, city1, city2):
        if arrive_city1 < 0 or arrive_city2 < 0:
            return True
        
        # If city2 is visited immediately after city1
        if depart_city1 + 1 == arrive_city2:
            return city2 in direct_flights.get(city1, [])
        
        # If city1 is visited immediately after city2  
        if depart_city2 + 1 == arrive_city1:
            return city1 in direct_flights.get(city2, [])
        
        return True
    
    # Add transition constraints for all city pairs
    for i, city1 in enumerate(cities):
        for j, city2 in enumerate(cities):
            if i < j:  # Avoid duplicate constraints
                problem.addConstraint(
                    lambda a1, d1, a2, d2, c1=city1, c2=city2: 
                    valid_transition(a1, d1, a2, d2, c1, c2),
                    [f'arrive_{city1}', f'depart_{city1}', 
                     f'arrive_{city2}', f'depart_{city2}']
                )
    
    # All days must be accounted for and no overlaps
    def valid_schedule(*args):
        # args: arrive_city1, depart_city1, arrive_city2, depart_city2, ...
        days_covered = set()
        
        for i in range(0, len(args), 2):
            arrive, depart = args[i], args[i+1]
            if arrive >= 0:
                for day in range(arrive, depart + 1):
                    if day in days_covered:
                        return False
                    days_covered.add(day)
        
        # Check if all days from 1 to 13 are covered
        return all(day in days_covered for day in range(1, total_days + 1))
    
    schedule_args = []
    for city in cities:
        schedule_args.extend([f'arrive_{city}', f'depart_{city}'])
    
    problem.addConstraint(valid_schedule, schedule_args)
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first solution
    solution = solutions[0]
    
    # Build the itinerary
    itinerary = []
    city_stays = []
    
    for city in cities:
        arrive = solution[f'arrive_{city}']
        depart = solution[f'depart_{city}']
        if arrive >= 0:
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