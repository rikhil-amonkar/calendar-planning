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
    
    # Define arrival day for each city (day 1-13)
    for city in cities:
        problem.addVariable(f'arrive_{city}', range(1, total_days + 1))
    
    # Direct flight constraints
    direct_flights = {
        'Porto': ['Stuttgart', 'Seville', 'Madrid'],
        'Stuttgart': ['Porto'],
        'Seville': ['Porto', 'Madrid'],
        'Madrid': ['Porto', 'Seville']
    }
    
    def all_constraints(*arrivals):
        # Unpack arrivals
        arrive_porto, arrive_stuttgart, arrive_seville, arrive_madrid = arrivals
        depart_porto = arrive_porto + 2
        depart_stuttgart = arrive_stuttgart + 6
        depart_seville = arrive_seville + 1
        depart_madrid = arrive_madrid + 3
        
        # 1. Stuttgart conference: must be in Stuttgart on day 7 AND day 13
        # This means Stuttgart must start on or before day 7 and end on or after day 13
        if not (arrive_stuttgart <= 7 and depart_stuttgart >= 13):
            return False
        
        # 2. Madrid relatives: visit must be between day 1 and day 4
        if not (arrive_madrid >= 1 and depart_madrid <= 4):
            return False
        
        # 3. No overlapping stays
        stays = [
            ('Porto', arrive_porto, depart_porto),
            ('Stuttgart', arrive_stuttgart, depart_stuttgart),
            ('Seville', arrive_seville, depart_seville),
            ('Madrid', arrive_madrid, depart_madrid)
        ]
        
        # Check for overlaps
        for i in range(len(stays)):
            for j in range(i + 1, len(stays)):
                city1, start1, end1 = stays[i]
                city2, start2, end2 = stays[j]
                if not (end1 < start2 or end2 < start1):
                    return False
        
        # 4. All days must be covered exactly once (no gaps)
        all_days = set(range(1, total_days + 1))
        covered_days = set()
        
        for city, start, end in stays:
            city_days = set(range(start, end + 1))
            # Check if this city's days overlap with already covered days
            if covered_days & city_days:
                return False
            covered_days.update(city_days)
        
        if covered_days != all_days:
            return False
        
        # 5. Direct flight constraints between consecutive cities
        # Sort cities by arrival day to determine the sequence
        sorted_stays = sorted(stays, key=lambda x: x[1])
        
        for i in range(len(sorted_stays) - 1):
            current_city = sorted_stays[i][0]
            next_city = sorted_stays[i + 1][0]
            current_end = sorted_stays[i][2]
            next_start = sorted_stays[i + 1][1]
            
            # Check if consecutive (no gaps between stays)
            if current_end + 1 != next_start:
                return False
            
            # Check if direct flight exists
            if next_city not in direct_flights[current_city]:
                return False
        
        return True
    
    # Apply all constraints
    arrival_vars = ['arrive_Porto', 'arrive_Stuttgart', 'arrive_Seville', 'arrive_Madrid']
    problem.addConstraint(all_constraints, arrival_vars)
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first solution
    solution = solutions[0]
    
    # Build itinerary
    itinerary = []
    
    # Create stay information
    stays = []
    for city in cities:
        arrive = solution[f'arrive_{city}']
        depart = arrive + cities[city] - 1
        stays.append({
            'city': city,
            'arrive': arrive,
            'depart': depart
        })
    
    # Sort by arrival day
    stays.sort(key=lambda x: x['arrive'])
    
    # Create day ranges for output
    for stay in stays:
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