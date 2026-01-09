from constraint import Problem
import json

def main():
    problem = Problem()
    
    # Define cities and their required days
    cities = {
        'Venice': 4,
        'Barcelona': 3,
        'Copenhagen': 4,
        'Lyon': 4,
        'Reykjavik': 4,
        'Dubrovnik': 5,
        'Athens': 2,
        'Tallinn': 5,
        'Munich': 3
    }
    
    # Define direct flight connections
    connections = {
        'Copenhagen': ['Athens', 'Dubrovnik', 'Munich', 'Reykjavik', 'Venice', 'Barcelona', 'Tallinn'],
        'Munich': ['Tallinn', 'Copenhagen', 'Venice', 'Reykjavik', 'Athens', 'Lyon', 'Barcelona', 'Dubrovnik'],
        'Venice': ['Munich', 'Athens', 'Copenhagen', 'Lyon', 'Barcelona'],
        'Reykjavik': ['Athens', 'Copenhagen', 'Munich', 'Barcelona'],
        'Athens': ['Copenhagen', 'Dubrovnik', 'Venice', 'Munich', 'Barcelona'],
        'Lyon': ['Barcelona', 'Munich', 'Venice'],
        'Barcelona': ['Lyon', 'Reykjavik', 'Dubrovnik', 'Athens', 'Copenhagen', 'Venice', 'Munich', 'Tallinn'],
        'Dubrovnik': ['Copenhagen', 'Athens', 'Barcelona', 'Munich'],
        'Tallinn': ['Munich', 'Copenhagen', 'Barcelona']
    }
    
    # Total days
    total_days = 26
    
    # Define variables for start day of each city
    for city in cities:
        problem.addVariable(f"{city}_start", range(1, total_days - cities[city] + 2))
    
    # Constraint: all cities must be visited
    # Constraint: cities cannot overlap (allowing 1 day for travel)
    city_list = list(cities.keys())
    for i in range(len(city_list)):
        for j in range(i + 1, len(city_list)):
            city1, city2 = city_list[i], city_list[j]
            duration1, duration2 = cities[city1], cities[city2]
            
            # Cities cannot overlap (end of city1 + 1 < start of city2 OR end of city2 + 1 < start of city1)
            problem.addConstraint(
                lambda s1, s2, dur1=duration1, dur2=duration2: 
                    (s1 + dur1 <= s2) or (s2 + dur2 <= s1),
                [f"{city1}_start", f"{city2}_start"]
            )
    
    # Special constraints (revised to be less restrictive)
    # Barcelona must include some days between 10 and 12
    problem.addConstraint(
        lambda start: start <= 12 and start + 2 >= 10,  # 3-day stay must overlap with days 10-12
        ["Barcelona_start"]
    )
    
    # Copenhagen must include some days between 7 and 10
    problem.addConstraint(
        lambda start: start <= 10 and start + 3 >= 7,  # 4-day stay must overlap with days 7-10
        ["Copenhagen_start"]
    )
    
    # Dubrovnik must include some days between 16 and 20
    problem.addConstraint(
        lambda start: start <= 20 and start + 4 >= 16,  # 5-day stay must overlap with days 16-20
        ["Dubrovnik_start"]
    )
    
    # Find a solution
    solution = problem.getSolution()
    
    if not solution:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Create itinerary with day ranges
    itinerary = []
    city_stays = []
    
    for city in cities:
        start = solution[f"{city}_start"]
        end = start + cities[city] - 1
        city_stays.append((start, end, city))
    
    # Sort by start day
    city_stays.sort()
    
    # Build itinerary with day ranges
    for start, end, city in city_stays:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Verify flight connectivity
    valid_itinerary = True
    for i in range(len(city_stays) - 1):
        current_city = city_stays[i][2]
        next_city = city_stays[i + 1][2]
        
        if next_city not in connections[current_city]:
            valid_itinerary = False
            break
    
    if not valid_itinerary:
        print(json.dumps({"error": "No valid itinerary found with flight connections"}))
        return
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()